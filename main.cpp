#include <iostream>
#include <vector>
#include <unordered_set>
#include <bitset>
#include <utility>
#include <algorithm>
#include <random>
#include <cassert>
#include <chrono>
#include <set>
#include <unordered_map>

namespace std {
    template<>
    struct hash<std::pair<int, int>> {
        inline size_t operator()(const std::pair<int, int> &v) const {
            std::hash<int> int_hasher;
            return int_hasher(v.first) ^ int_hasher(v.second);
        }
    };
}

template<int sudoku_size=3>
class sudoku
{
    std::vector<std::vector<std::unordered_set<int>>> grid;
    using couple = std::pair<int,int>;
    int depth;
    inline static constexpr int d=sudoku_size;
    inline static constexpr int n=sudoku_size*sudoku_size;
    inline static constexpr int m=n;
    inline static constexpr int r=n;
    std::unordered_set<couple> recently_proven_unique;
    std::vector<std::vector<std::unordered_map<int,std::unordered_set<couple>> >> box_value_cell_mapper;
    std::vector<std::unordered_map<int,std::unordered_set<couple>>> row_value_cell_mapper,col_value_cell_mapper;
public:
    inline static int counter=0;
    enum class State{solvable,solved,unsolvable=-1}state;
    sudoku():depth(0),grid(n,std::vector<std::unordered_set<int>>(m)),state(State::solvable)
    {
        for(auto &R:grid) for(auto &cell:R) for(int i=1;i<=n;i++)
            cell.insert(i);
    }
    sudoku(const std::vector<std::vector<int>> &G):sudoku()
    {
        for(int i=0;i<n;i++)
            for(int j=0;j<m;j++)
                if(G[i][j]) {
                    grid[i][j] = {G[i][j]};
                    recently_proven_unique.insert({i,j});
                }
    }
    bool row_integrity(int i) const
    {
        std::bitset<n> rule;
        for(int j=0;j<n;j++)
            for(auto &c:grid[i][j])
                rule[c]=true;
        bool R= rule.count()>=n;
        return R;
    }

    bool column_integrity(int j) const
    {
        std::bitset<n> rule;
        for(int i=0;i<n;i++)
            for(auto &c:grid[i][j])
                rule[c]=true;
        bool R= rule.count()>=n;
        return R;
    }

    bool box_integrity(int a,int b) const
    {
        std::bitset<n> rule;
        for(int i=0;i<d;i++)
            for(int j=0;j<d;j++)
                for(auto &c:grid[d*a+i][d*b+j])
                    rule[c]=true;
        bool R= rule.count()>=n;
        return R;
    }

    bool redundancy_elimination(int i,int j)
    {
        bool any_elimination=false;
        couple box = {i/d,j/d};
        if(grid[i][j].size()==1)
        {
            auto cell_value = *grid[i][j].begin();
            for (int w = 0; w < n; w++)
            {
                if(w==j)
                    continue;
                if (grid[i][w].contains(cell_value)) any_elimination = true;
                grid[i][w].erase(cell_value);
            }
            for (int w = 0; w < n; w++)
            {
                if(w==i)
                    continue;
                if (grid[w][j].contains(cell_value)) any_elimination = true;
                grid[w][j].erase(cell_value);
            }
            for (int w1 = 0; w1 < d; w1++) for(int w2=0;w2<d;w2++)
                {
                    int a=d*box.first+w1,b=d*box.second+w2;
                    if(i==a && j==b)
                        continue;
                    if (grid[a][b].contains(cell_value)) any_elimination = true;
                    grid[a][b].erase(cell_value);
                }
        }
        return any_elimination;
    }

    bool redundancy_elimination()
    {
        std::unordered_set<couple> recent_uniqueness_set;
        bool any_elimination = false;
        for(auto [i,j]:recently_proven_unique)
        {
            if(grid[i][j].empty())
            {
                state=State::unsolvable;
                return false;
            }
            couple box = {i / d, j / d};
            auto cell_value = *grid[i][j].begin();
            for (int w = 0; w < n; w++)
            {
                if (w == j)
                    continue;
                if (grid[i][w].contains(cell_value))
                {
                    any_elimination = true;
                    grid[i][w].erase(cell_value);
                    if (grid[i][w].size() == 1)
                        recent_uniqueness_set.insert({i, w});
                    else if(grid[i][w].empty()) {
                        state=State::unsolvable;
                        return false;
                    }
                }
            }
            for (int w = 0; w < n; w++)
            {
                if (w == i)
                    continue;
                if (grid[w][j].contains(cell_value))
                {
                    any_elimination = true;
                    grid[w][j].erase(cell_value);
                    if (grid[w][j].size() == 1)
                        recent_uniqueness_set.insert({w, j});
                    else if(grid[w][j].empty()) {
                        state=State::unsolvable;
                        return false;
                    }
                }
            }
            for (int w1 = 0; w1 < d; w1++)
                for (int w2 = 0; w2 < d; w2++) {
                    int a = d * box.first + w1, b = d * box.second + w2;
                    if (i == a && j == b)
                        continue;
                    if (grid[a][b].contains(cell_value))
                    {
                        any_elimination = true;
                        grid[a][b].erase(cell_value);
                        if (grid[a][b].size() == 1)
                            recent_uniqueness_set.insert({a, b});
                        else if(grid[a][b].empty()) {
                            state=State::unsolvable;
                            return false;
                        }
                    }
                }
        }
        recently_proven_unique=std::move(recent_uniqueness_set);
        return any_elimination;
    }

/*
 * The two cells must be on the same box
 */
    bool parallel_redundancy_elimination(int v,int i1,int j1,int i2,int j2)
    {
        bool any_elimination=false;
        bool row_aligned = i1==i2;
        assert(std::make_pair(i1/d,j1/d)==std::make_pair(i2/d,j2/d));
        couple box=std::make_pair(i1/d,j1/d);
        if(grid[i1][j1].size()!=2|| grid[i2][j2].size()!=2)
            return false;
        if(row_aligned) for(int k=0;k<d;k++) if(k!=box.first) for(int s=0;s<d;s++)
                    {
                        /*
                         * d = sum(i,0,2)
                         */
                        if(grid[d*k+s][j1].size()==2 && grid[d*k+s][j2].size()==2 &&
                           grid[d*k+s][j1].contains(v) && grid[d*k+s][j2].contains(v))
                        {
                            int affected_box_row = d - box.first - k;
                            for(int p=0;p<d;p++) {
                                grid[d * affected_box_row + p][j1].erase(v);
                                grid[d * affected_box_row + p][j2].erase(v);
                                if(grid[d * affected_box_row + p][j1].size()==1)
                                    recently_proven_unique.insert({d * affected_box_row + p,j1});
                                if(grid[d * affected_box_row + p][j2].size()==1)
                                    recently_proven_unique.insert({d * affected_box_row + p,j2});
                            }
                            return true;
                        }
                    }
                else for(int k=0;k<d;k++) if(k!=box.second) for(int s=0;s<d;s++)
                            {
                                /*
                                 * d = sum(i,0,2)
                                 */
                                if(grid[i1][d*k+s].size()==2 && grid[i2][d*k+s].size()==2 &&
                                   grid[i1][d*k+s].contains(v) && grid[i2][d*k+s].contains(v))
                                {
                                    int affected_box_column = d - box.second - k;
                                    for(int p=0;p<d;p++) {
                                        grid[i1][d * affected_box_column + p].erase(v);
                                        grid[i2][d * affected_box_column + p].erase(v);
                                        if(grid[i1][d * affected_box_column + p].size()==1)
                                            recently_proven_unique.insert({i1,d * affected_box_column + p});
                                        if(grid[i2][d * affected_box_column + p].size()==1)
                                            recently_proven_unique.insert({i2,d * affected_box_column + p});
                                    }
                                    return true;
                                }
                            }
        return false;
    }

    bool multiple_redundancy_elimination(int i,int j)
    {
        bool any_elimination=false;
        couple box = {i/d,j/d};
        auto size=grid[i][j].size();
        if(size>1 && size<d) for(const auto &cell:grid[i][j])
            {
                auto cell_value = cell;
                std::vector<std::pair<int,int>> all_pos;
                all_pos.emplace_back(i,j);
                for(int w1=0;w1<d;w1++) for(int w2=0;w2<d;w2++)
                    {
                        int a=d * box.first + w1,b=d * box.second + w2;
                        if (a == i && b == j)
                            continue;
                        if(grid[a][b].contains(cell_value))
                            all_pos.emplace_back(a,b);
                    }
                bool row_aligned=std::all_of(all_pos.begin(),all_pos.end(),[i](const auto &P){return P.first==i;}),
                        column_aligned=std::all_of(all_pos.begin(),all_pos.end(),[j](const auto &P){return P.second==j;});
                if(row_aligned)
                {
                    std::unordered_set<int> col_set;
                    for(auto &s:all_pos)
                        col_set.insert(s.second);
                    for (int w = 0; w < n; w++) {
                        if (col_set.contains(w))
                            continue;
                        if (grid[i][w].contains(cell_value)) {
                            any_elimination = true;
                            grid[i][w].erase(cell_value);
                            if( grid[i][w].size()==1)
                                recently_proven_unique.insert({i,w});

                        }
                    }
                    //auto [p,q]=all_pos.back();
                    //any_elimination|=parallel_redundancy_elimination(cell,i,j,p,q);
                }
                if(column_aligned)
                {
                    std::unordered_set<int> row_set;
                    for(auto &s:all_pos)
                        row_set.insert(s.first);
                    for (int w = 0; w < n; w++) {
                        if (row_set.contains(w))
                            continue;
                        if (grid[w][j].contains(cell_value)) {
                            any_elimination = true;
                            grid[w][j].erase(cell_value);
                            if( grid[w][j].size()==1)
                                recently_proven_unique.insert({w,j});
                        }
                    }
                    //auto [p,q]=all_pos.back();
                    //any_elimination|=parallel_redundancy_elimination(cell,i,j,p,q);
                }

            }
        return any_elimination;
    }


    bool integrity_check()
    {
        for(int i=0;i<n;i++)
            if(!column_integrity(i))
            {
                state=State::unsolvable;
                return false;
            }
        for(int i=0;i<n;i++) if(!row_integrity(i)) {state=State::unsolvable;return false;}
        for(int i=0;i<d;i++) for(int j=0;j<d;j++) if(!box_integrity(i,j)) {state=State::unsolvable;return false;}
        return true;
    }
    bool check_solved()
    {
        if(state==State::unsolvable)
            return false;
        for(int i=0;i<n;i++)
            for(int j=0;j<n;j++)
                if(grid[i][j].size() !=1)
                    return false;
        state=State::solved;
        return true;
    }

    std::vector<std::vector<int>> solve()
    {
        while(state==State::solvable)
        {
            counter++;
            bool any_elimination=false;
            any_elimination|=redundancy_elimination();
            for(int i=0;i<n;i++)
                for(int j=0;j<n;j++)
                {
                    //any_elimination|=redundancy_elimination(i,j);
                    any_elimination|=multiple_redundancy_elimination(i,j);
                }

            bool I=integrity_check();
            bool S=check_solved();
            if(S)
                break;
            if(!any_elimination && I)
            {
                int a=-1,b=-1;
                for(int i=0;i<n;i++)
                {
                    for (int j = 0; j < n; j++)
                        if (grid[i][j].size() > 1 && a==-1) {
                            a = i;
                            b = j;
                        }
                        else if(grid[i][j].size()>1&&grid[i][j].size()<grid[a][b].size())
                        {
                            a=i;
                            b=j;
                        }
                }
                std::unordered_set<int> values=grid[a][b];
                for(const auto &s:values)
                {
                    sudoku sub_sudoku=*this;
                    sub_sudoku.grid[a][b]={s};
                    sub_sudoku.recently_proven_unique.insert({a,b});
                    //for(int i=0;i<n;i++) for(int j=0;j<n;j++) if(grid[i][j].size()==1) sub_sudoku.recently_proven_unique.insert({i,j});
                    auto solution=sub_sudoku.solve();
                    depth=std::max(sub_sudoku.depth+1,depth);
                    if(sub_sudoku.state==State::solved) {
                        state=State::solved;
                        return solution;
                    }
                }
                state=State::unsolvable;
                return {};
            }
        }
        if(state==State::unsolvable)
            return {};
        std::vector<std::vector<int>> solution(n,std::vector<int>(n));
        for(int i=0;i<n;i++) for(int j=0;j<n;j++)
                solution[i][j]= *grid[i][j].begin();
        return solution;
    }

    int get_depth() const
    {
        return depth;
    }
};

constexpr int sudoku_size=5;
int main() {
    std::vector<std::vector<int>> G(sudoku_size*sudoku_size,std::vector<int>(sudoku_size*sudoku_size,0));
    for(auto &R:G) for(auto &v:R)
            std::cin >> v;
    sudoku<sudoku_size> S(G);
    auto t1=std::chrono::high_resolution_clock::now();
    auto solution = S.solve();
    auto t2 = std::chrono::high_resolution_clock::now();
    if(solution.empty())
        std::cout << "This sudoku is unsolvable";
    else
    {
        std::cout << "Solution Depth:" << S.get_depth()<< std::endl;
        std::cout << "Counter:" << S.counter<< std::endl;
        for (const auto &R:solution) {
            for (const auto &v:R)
                std::cout << v << ' ';
            std::cout << '\n';
        }
    }
    std::cout << "Time Elapsed: " << std::chrono::duration_cast<std::chrono::milliseconds>(t2-t1).count()<<" ms";
    return 0;
}
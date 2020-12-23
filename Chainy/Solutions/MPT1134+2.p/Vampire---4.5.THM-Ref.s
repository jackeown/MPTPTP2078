%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1134+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:09 EST 2020

% Result     : Theorem 2.76s
% Output     : Refutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 130 expanded)
%              Number of leaves         :   18 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :  233 ( 461 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4986,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2138,f2139,f2144,f2149,f2344,f2393,f3046,f3180,f3195,f4921,f4974])).

fof(f4974,plain,
    ( ~ spl25_1
    | ~ spl25_4
    | spl25_369 ),
    inference(avatar_contradiction_clause,[],[f4973])).

fof(f4973,plain,
    ( $false
    | ~ spl25_1
    | ~ spl25_4
    | spl25_369 ),
    inference(trivial_inequality_removal,[],[f4969])).

fof(f4969,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ spl25_1
    | ~ spl25_4
    | spl25_369 ),
    inference(unit_resulting_resolution,[],[f2148,f2132,f4920,f2127])).

fof(f2127,plain,(
    ! [X2,X0,X3] :
      ( sP24(X3,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f2127_D])).

fof(f2127_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
          | ~ l1_pre_topc(X2)
          | ~ m1_pre_topc(X2,X0) )
    <=> ~ sP24(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP24])])).

fof(f4920,plain,
    ( ~ sP24(sK3,sK4)
    | spl25_369 ),
    inference(avatar_component_clause,[],[f4918])).

fof(f4918,plain,
    ( spl25_369
  <=> sP24(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_369])])).

fof(f2132,plain,
    ( m1_pre_topc(sK3,sK4)
    | ~ spl25_1 ),
    inference(avatar_component_clause,[],[f2131])).

fof(f2131,plain,
    ( spl25_1
  <=> m1_pre_topc(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_1])])).

fof(f2148,plain,
    ( l1_pre_topc(sK3)
    | ~ spl25_4 ),
    inference(avatar_component_clause,[],[f2146])).

fof(f2146,plain,
    ( spl25_4
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_4])])).

fof(f4921,plain,
    ( ~ spl25_369
    | spl25_2
    | ~ spl25_3
    | ~ spl25_4
    | ~ spl25_43
    | ~ spl25_154 ),
    inference(avatar_split_clause,[],[f4878,f3173,f2399,f2146,f2141,f2135,f4918])).

fof(f2135,plain,
    ( spl25_2
  <=> m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_2])])).

fof(f2141,plain,
    ( spl25_3
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_3])])).

fof(f2399,plain,
    ( spl25_43
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_43])])).

fof(f3173,plain,
    ( spl25_154
  <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_154])])).

fof(f4878,plain,
    ( ~ sP24(sK3,sK4)
    | spl25_2
    | ~ spl25_3
    | ~ spl25_4
    | ~ spl25_43
    | ~ spl25_154 ),
    inference(unit_resulting_resolution,[],[f2148,f2143,f2400,f2137,f3175,f2128])).

fof(f2128,plain,(
    ! [X0,X3,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | m1_pre_topc(X3,X1)
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ sP24(X3,X0) ) ),
    inference(general_splitting,[],[f2028,f2127_D])).

fof(f2028,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1874])).

fof(f1874,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1873])).

fof(f1873,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1829])).

fof(f1829,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( l1_pre_topc(X2)
             => ! [X3] :
                  ( l1_pre_topc(X3)
                 => ( ( m1_pre_topc(X2,X0)
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).

fof(f3175,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl25_154 ),
    inference(avatar_component_clause,[],[f3173])).

fof(f2137,plain,
    ( ~ m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | spl25_2 ),
    inference(avatar_component_clause,[],[f2135])).

fof(f2400,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl25_43 ),
    inference(avatar_component_clause,[],[f2399])).

fof(f2143,plain,
    ( l1_pre_topc(sK4)
    | ~ spl25_3 ),
    inference(avatar_component_clause,[],[f2141])).

fof(f3195,plain,
    ( spl25_155
    | ~ spl25_35 ),
    inference(avatar_split_clause,[],[f3194,f2341,f3177])).

fof(f3177,plain,
    ( spl25_155
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_155])])).

fof(f2341,plain,
    ( spl25_35
  <=> m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_35])])).

fof(f3194,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl25_35 ),
    inference(unit_resulting_resolution,[],[f2343,f2015])).

fof(f2015,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f1865])).

fof(f1865,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1777])).

fof(f1777,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f2343,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ spl25_35 ),
    inference(avatar_component_clause,[],[f2341])).

fof(f3180,plain,
    ( spl25_154
    | ~ spl25_155
    | ~ spl25_43 ),
    inference(avatar_split_clause,[],[f3070,f2399,f3177,f3173])).

fof(f3070,plain,
    ( ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl25_43 ),
    inference(resolution,[],[f2400,f2030])).

fof(f2030,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f1878])).

fof(f1878,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1877])).

fof(f1877,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1759])).

fof(f1759,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f3046,plain,
    ( ~ spl25_35
    | spl25_43 ),
    inference(avatar_split_clause,[],[f3008,f2399,f2341])).

fof(f3008,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | spl25_43 ),
    inference(resolution,[],[f2401,f2016])).

fof(f2016,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f1865])).

fof(f2401,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | spl25_43 ),
    inference(avatar_component_clause,[],[f2399])).

fof(f2393,plain,
    ( ~ spl25_3
    | ~ spl25_2
    | spl25_1 ),
    inference(avatar_split_clause,[],[f2388,f2131,f2135,f2141])).

fof(f2388,plain,
    ( ~ m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(sK4)
    | spl25_1 ),
    inference(resolution,[],[f2027,f2133])).

fof(f2133,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | spl25_1 ),
    inference(avatar_component_clause,[],[f2131])).

fof(f2027,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1872])).

fof(f1872,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1848])).

fof(f1848,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f2344,plain,
    ( spl25_35
    | ~ spl25_3 ),
    inference(avatar_split_clause,[],[f2327,f2141,f2341])).

fof(f2327,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ spl25_3 ),
    inference(unit_resulting_resolution,[],[f2143,f2060])).

fof(f2060,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1887])).

fof(f1887,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1786])).

fof(f1786,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f2149,plain,(
    spl25_4 ),
    inference(avatar_split_clause,[],[f2009,f2146])).

fof(f2009,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f1952])).

fof(f1952,plain,
    ( ( ~ m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
      | ~ m1_pre_topc(sK3,sK4) )
    & ( m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
      | m1_pre_topc(sK3,sK4) )
    & l1_pre_topc(sK4)
    & l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f1949,f1951,f1950])).

fof(f1950,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | m1_pre_topc(X0,X1) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | ~ m1_pre_topc(sK3,X1) )
          & ( m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | m1_pre_topc(sK3,X1) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f1951,plain,
    ( ? [X1] :
        ( ( ~ m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ m1_pre_topc(sK3,X1) )
        & ( m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | m1_pre_topc(sK3,X1) )
        & l1_pre_topc(X1) )
   => ( ( ~ m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
        | ~ m1_pre_topc(sK3,sK4) )
      & ( m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
        | m1_pre_topc(sK3,sK4) )
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f1949,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | ~ m1_pre_topc(X0,X1) )
          & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | m1_pre_topc(X0,X1) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1948])).

fof(f1948,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | ~ m1_pre_topc(X0,X1) )
          & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | m1_pre_topc(X0,X1) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f1863])).

fof(f1863,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_pre_topc(X0,X1)
          <~> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1856])).

fof(f1856,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( m1_pre_topc(X0,X1)
            <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    inference(negated_conjecture,[],[f1855])).

fof(f1855,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f2144,plain,(
    spl25_3 ),
    inference(avatar_split_clause,[],[f2010,f2141])).

fof(f2010,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f1952])).

fof(f2139,plain,
    ( spl25_1
    | spl25_2 ),
    inference(avatar_split_clause,[],[f2011,f2135,f2131])).

fof(f2011,plain,
    ( m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f1952])).

fof(f2138,plain,
    ( ~ spl25_1
    | ~ spl25_2 ),
    inference(avatar_split_clause,[],[f2012,f2135,f2131])).

fof(f2012,plain,
    ( ~ m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f1952])).
%------------------------------------------------------------------------------

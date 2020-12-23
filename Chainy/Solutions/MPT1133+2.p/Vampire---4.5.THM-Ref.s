%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1133+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:08 EST 2020

% Result     : Theorem 17.15s
% Output     : Refutation 17.15s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 626 expanded)
%              Number of leaves         :   31 ( 230 expanded)
%              Depth                    :   23
%              Number of atoms          : 1373 (4822 expanded)
%              Number of equality atoms :   49 ( 484 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15543,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2433,f2438,f2443,f2448,f2453,f2521,f2583,f2624,f2680,f2689,f2695,f3061,f3066,f3247,f9398,f13162,f15093,f15166,f15384,f15403,f15503,f15542])).

fof(f15542,plain,
    ( ~ spl39_1
    | ~ spl39_2
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | ~ spl39_11
    | ~ spl39_52
    | ~ spl39_375
    | spl39_381 ),
    inference(avatar_contradiction_clause,[],[f15541])).

fof(f15541,plain,
    ( $false
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | ~ spl39_11
    | ~ spl39_52
    | ~ spl39_375
    | spl39_381 ),
    inference(subsumption_resolution,[],[f15382,f15524])).

fof(f15524,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | ~ spl39_11
    | ~ spl39_52
    | ~ spl39_375 ),
    inference(subsumption_resolution,[],[f15523,f2520])).

fof(f2520,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl39_6 ),
    inference(avatar_component_clause,[],[f2518])).

fof(f2518,plain,
    ( spl39_6
  <=> v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_6])])).

fof(f15523,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | ~ spl39_11
    | ~ spl39_52
    | ~ spl39_375 ),
    inference(forward_demodulation,[],[f15522,f13353])).

fof(f13353,plain,
    ( u1_struct_0(sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_52
    | ~ spl39_375 ),
    inference(trivial_inequality_removal,[],[f13350])).

fof(f13350,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | u1_struct_0(sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_52
    | ~ spl39_375 ),
    inference(superposition,[],[f3300,f13161])).

fof(f13161,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_375 ),
    inference(avatar_component_clause,[],[f13159])).

fof(f13159,plain,
    ( spl39_375
  <=> g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_375])])).

fof(f3300,plain,
    ( ! [X4,X3] :
        ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X3,X4)
        | u1_struct_0(sK3) = X3 )
    | ~ spl39_52 ),
    inference(resolution,[],[f3246,f2165])).

fof(f2165,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f1877])).

fof(f1877,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1806])).

fof(f1806,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f3246,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ spl39_52 ),
    inference(avatar_component_clause,[],[f3244])).

fof(f3244,plain,
    ( spl39_52
  <=> m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_52])])).

fof(f15522,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | ~ spl39_11
    | ~ spl39_52
    | ~ spl39_375 ),
    inference(subsumption_resolution,[],[f15521,f2582])).

fof(f2582,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl39_7 ),
    inference(avatar_component_clause,[],[f2580])).

fof(f2580,plain,
    ( spl39_7
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_7])])).

fof(f15521,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | ~ spl39_11
    | ~ spl39_52
    | ~ spl39_375 ),
    inference(forward_demodulation,[],[f15520,f13353])).

fof(f15520,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | ~ spl39_11 ),
    inference(subsumption_resolution,[],[f15519,f2432])).

fof(f2432,plain,
    ( v2_pre_topc(sK2)
    | ~ spl39_1 ),
    inference(avatar_component_clause,[],[f2430])).

fof(f2430,plain,
    ( spl39_1
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_1])])).

fof(f15519,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v2_pre_topc(sK2)
    | ~ spl39_2
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | ~ spl39_11 ),
    inference(subsumption_resolution,[],[f15518,f2437])).

fof(f2437,plain,
    ( l1_pre_topc(sK2)
    | ~ spl39_2 ),
    inference(avatar_component_clause,[],[f2435])).

fof(f2435,plain,
    ( spl39_2
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_2])])).

fof(f15518,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | ~ spl39_11 ),
    inference(subsumption_resolution,[],[f15517,f2442])).

fof(f2442,plain,
    ( v2_pre_topc(sK3)
    | ~ spl39_3 ),
    inference(avatar_component_clause,[],[f2440])).

fof(f2440,plain,
    ( spl39_3
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_3])])).

fof(f15517,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | ~ spl39_11 ),
    inference(subsumption_resolution,[],[f15516,f2447])).

fof(f2447,plain,
    ( l1_pre_topc(sK3)
    | ~ spl39_4 ),
    inference(avatar_component_clause,[],[f2445])).

fof(f2445,plain,
    ( spl39_4
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_4])])).

fof(f15516,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | ~ spl39_11 ),
    inference(subsumption_resolution,[],[f15515,f2520])).

fof(f15515,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_5
    | ~ spl39_7
    | ~ spl39_11 ),
    inference(subsumption_resolution,[],[f15514,f2582])).

fof(f15514,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_5
    | ~ spl39_11 ),
    inference(subsumption_resolution,[],[f2699,f2452])).

fof(f2452,plain,
    ( v1_funct_1(sK5)
    | ~ spl39_5 ),
    inference(avatar_component_clause,[],[f2450])).

fof(f2450,plain,
    ( spl39_5
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_5])])).

fof(f2699,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_11 ),
    inference(resolution,[],[f2683,f2425])).

fof(f2425,plain,(
    ! [X0,X3,X1] :
      ( ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f2397])).

fof(f2397,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f2139])).

fof(f2139,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2033])).

fof(f2033,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f1862])).

fof(f1862,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f1861])).

fof(f1861,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1853])).

fof(f1853,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f2683,plain,
    ( v5_pre_topc(sK5,sK2,sK3)
    | ~ spl39_11 ),
    inference(avatar_component_clause,[],[f2682])).

fof(f2682,plain,
    ( spl39_11
  <=> v5_pre_topc(sK5,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_11])])).

fof(f15382,plain,
    ( ~ v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | spl39_381 ),
    inference(avatar_component_clause,[],[f15381])).

fof(f15381,plain,
    ( spl39_381
  <=> v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_381])])).

fof(f15503,plain,
    ( ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | spl39_12
    | ~ spl39_47
    | ~ spl39_52
    | ~ spl39_148
    | ~ spl39_375
    | ~ spl39_379
    | ~ spl39_380
    | ~ spl39_381 ),
    inference(avatar_contradiction_clause,[],[f15502])).

fof(f15502,plain,
    ( $false
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | spl39_12
    | ~ spl39_47
    | ~ spl39_52
    | ~ spl39_148
    | ~ spl39_375
    | ~ spl39_379
    | ~ spl39_380
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f2688,f15461])).

fof(f15461,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | ~ spl39_47
    | ~ spl39_52
    | ~ spl39_148
    | ~ spl39_375
    | ~ spl39_379
    | ~ spl39_380
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f15460,f2520])).

fof(f15460,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_7
    | ~ spl39_47
    | ~ spl39_52
    | ~ spl39_148
    | ~ spl39_375
    | ~ spl39_379
    | ~ spl39_380
    | ~ spl39_381 ),
    inference(forward_demodulation,[],[f15459,f13353])).

fof(f15459,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_7
    | ~ spl39_47
    | ~ spl39_52
    | ~ spl39_148
    | ~ spl39_375
    | ~ spl39_379
    | ~ spl39_380
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f15458,f2582])).

fof(f15458,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_47
    | ~ spl39_52
    | ~ spl39_148
    | ~ spl39_375
    | ~ spl39_379
    | ~ spl39_380
    | ~ spl39_381 ),
    inference(forward_demodulation,[],[f15457,f13353])).

fof(f15457,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_47
    | ~ spl39_52
    | ~ spl39_148
    | ~ spl39_375
    | ~ spl39_379
    | ~ spl39_380
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f15456,f15092])).

fof(f15092,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
    | ~ spl39_379 ),
    inference(avatar_component_clause,[],[f15090])).

fof(f15090,plain,
    ( spl39_379
  <=> v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_379])])).

fof(f15456,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_47
    | ~ spl39_52
    | ~ spl39_148
    | ~ spl39_375
    | ~ spl39_380
    | ~ spl39_381 ),
    inference(forward_demodulation,[],[f15455,f13353])).

fof(f15455,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_47
    | ~ spl39_52
    | ~ spl39_148
    | ~ spl39_375
    | ~ spl39_380
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f15454,f15165])).

fof(f15165,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
    | ~ spl39_380 ),
    inference(avatar_component_clause,[],[f15163])).

fof(f15163,plain,
    ( spl39_380
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_380])])).

fof(f15454,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_47
    | ~ spl39_52
    | ~ spl39_148
    | ~ spl39_375
    | ~ spl39_381 ),
    inference(forward_demodulation,[],[f15453,f13353])).

fof(f15453,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_47
    | ~ spl39_148
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f15452,f2432])).

fof(f15452,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v2_pre_topc(sK2)
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_47
    | ~ spl39_148
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f15451,f2437])).

fof(f15451,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_5
    | ~ spl39_47
    | ~ spl39_148
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f15450,f3065])).

fof(f3065,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_47 ),
    inference(avatar_component_clause,[],[f3063])).

fof(f3063,plain,
    ( spl39_47
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_47])])).

fof(f15450,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_5
    | ~ spl39_148
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f15449,f9397])).

fof(f9397,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_148 ),
    inference(avatar_component_clause,[],[f9395])).

fof(f9395,plain,
    ( spl39_148
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_148])])).

fof(f15449,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_5
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f15390,f2452])).

fof(f15390,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_381 ),
    inference(resolution,[],[f15383,f2423])).

fof(f2423,plain,(
    ! [X0,X3,X1] :
      ( ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f2395])).

fof(f2395,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f2137])).

fof(f2137,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2032])).

fof(f2032,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f1860])).

fof(f1860,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f1859])).

fof(f1859,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1852])).

fof(f1852,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f15383,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_381 ),
    inference(avatar_component_clause,[],[f15381])).

fof(f2688,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | spl39_12 ),
    inference(avatar_component_clause,[],[f2686])).

fof(f2686,plain,
    ( spl39_12
  <=> v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_12])])).

fof(f15403,plain,
    ( ~ spl39_1
    | ~ spl39_2
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | spl39_11
    | ~ spl39_52
    | ~ spl39_375
    | ~ spl39_381 ),
    inference(avatar_contradiction_clause,[],[f15402])).

fof(f15402,plain,
    ( $false
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | spl39_11
    | ~ spl39_52
    | ~ spl39_375
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f15401,f2520])).

fof(f15401,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | spl39_11
    | ~ spl39_52
    | ~ spl39_375
    | ~ spl39_381 ),
    inference(forward_demodulation,[],[f15400,f13353])).

fof(f15400,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | spl39_11
    | ~ spl39_52
    | ~ spl39_375
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f15399,f2582])).

fof(f15399,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | spl39_11
    | ~ spl39_52
    | ~ spl39_375
    | ~ spl39_381 ),
    inference(forward_demodulation,[],[f15398,f13353])).

fof(f15398,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | spl39_11
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f15397,f2432])).

fof(f15397,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v2_pre_topc(sK2)
    | ~ spl39_2
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | spl39_11
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f15396,f2437])).

fof(f15396,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | spl39_11
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f15395,f2442])).

fof(f15395,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | spl39_11
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f15394,f2447])).

fof(f15394,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | spl39_11
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f15393,f2520])).

fof(f15393,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_5
    | ~ spl39_7
    | spl39_11
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f15392,f2582])).

fof(f15392,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_5
    | spl39_11
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f15391,f2452])).

fof(f15391,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl39_11
    | ~ spl39_381 ),
    inference(subsumption_resolution,[],[f15385,f2684])).

fof(f2684,plain,
    ( ~ v5_pre_topc(sK5,sK2,sK3)
    | spl39_11 ),
    inference(avatar_component_clause,[],[f2682])).

fof(f15385,plain,
    ( v5_pre_topc(sK5,sK2,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_381 ),
    inference(resolution,[],[f15383,f2424])).

fof(f2424,plain,(
    ! [X0,X3,X1] :
      ( ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f2396])).

fof(f2396,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f2140])).

fof(f2140,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2033])).

fof(f15384,plain,
    ( spl39_381
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | ~ spl39_10
    | ~ spl39_12
    | ~ spl39_47
    | ~ spl39_52
    | ~ spl39_148
    | ~ spl39_375
    | ~ spl39_379 ),
    inference(avatar_split_clause,[],[f15142,f15090,f13159,f9395,f3244,f3063,f2686,f2677,f2580,f2518,f2450,f2435,f2430,f15381])).

fof(f2677,plain,
    ( spl39_10
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_10])])).

fof(f15142,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | ~ spl39_10
    | ~ spl39_12
    | ~ spl39_47
    | ~ spl39_52
    | ~ spl39_148
    | ~ spl39_375
    | ~ spl39_379 ),
    inference(subsumption_resolution,[],[f15141,f2520])).

fof(f15141,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_7
    | ~ spl39_10
    | ~ spl39_12
    | ~ spl39_47
    | ~ spl39_52
    | ~ spl39_148
    | ~ spl39_375
    | ~ spl39_379 ),
    inference(forward_demodulation,[],[f15140,f13353])).

fof(f15140,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_7
    | ~ spl39_10
    | ~ spl39_12
    | ~ spl39_47
    | ~ spl39_52
    | ~ spl39_148
    | ~ spl39_375
    | ~ spl39_379 ),
    inference(subsumption_resolution,[],[f15139,f2582])).

fof(f15139,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_10
    | ~ spl39_12
    | ~ spl39_47
    | ~ spl39_52
    | ~ spl39_148
    | ~ spl39_375
    | ~ spl39_379 ),
    inference(forward_demodulation,[],[f15138,f13353])).

fof(f15138,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_10
    | ~ spl39_12
    | ~ spl39_47
    | ~ spl39_52
    | ~ spl39_148
    | ~ spl39_375
    | ~ spl39_379 ),
    inference(subsumption_resolution,[],[f15137,f15092])).

fof(f15137,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_10
    | ~ spl39_12
    | ~ spl39_47
    | ~ spl39_52
    | ~ spl39_148
    | ~ spl39_375 ),
    inference(forward_demodulation,[],[f15136,f13353])).

fof(f15136,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_10
    | ~ spl39_12
    | ~ spl39_47
    | ~ spl39_52
    | ~ spl39_148
    | ~ spl39_375 ),
    inference(subsumption_resolution,[],[f15135,f14989])).

fof(f14989,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
    | ~ spl39_10
    | ~ spl39_52
    | ~ spl39_375 ),
    inference(forward_demodulation,[],[f2679,f13353])).

fof(f2679,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ spl39_10 ),
    inference(avatar_component_clause,[],[f2677])).

fof(f15135,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_12
    | ~ spl39_47
    | ~ spl39_52
    | ~ spl39_148
    | ~ spl39_375 ),
    inference(forward_demodulation,[],[f15134,f13353])).

fof(f15134,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_1
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_12
    | ~ spl39_47
    | ~ spl39_148 ),
    inference(subsumption_resolution,[],[f15133,f2432])).

fof(f15133,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v2_pre_topc(sK2)
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_12
    | ~ spl39_47
    | ~ spl39_148 ),
    inference(subsumption_resolution,[],[f15132,f2437])).

fof(f15132,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_5
    | ~ spl39_12
    | ~ spl39_47
    | ~ spl39_148 ),
    inference(subsumption_resolution,[],[f15131,f3065])).

fof(f15131,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_5
    | ~ spl39_12
    | ~ spl39_148 ),
    inference(subsumption_resolution,[],[f15130,f9397])).

fof(f15130,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_5
    | ~ spl39_12 ),
    inference(subsumption_resolution,[],[f15124,f2452])).

fof(f15124,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl39_12 ),
    inference(resolution,[],[f2687,f2422])).

fof(f2422,plain,(
    ! [X0,X3,X1] :
      ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f2394])).

fof(f2394,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f2138])).

fof(f2138,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2032])).

fof(f2687,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_12 ),
    inference(avatar_component_clause,[],[f2686])).

fof(f15166,plain,
    ( spl39_380
    | ~ spl39_10
    | ~ spl39_52
    | ~ spl39_375 ),
    inference(avatar_split_clause,[],[f14989,f13159,f3244,f2677,f15163])).

fof(f15093,plain,
    ( spl39_379
    | ~ spl39_9
    | ~ spl39_52
    | ~ spl39_375 ),
    inference(avatar_split_clause,[],[f14996,f13159,f3244,f2621,f15090])).

fof(f2621,plain,
    ( spl39_9
  <=> v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_9])])).

fof(f14996,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
    | ~ spl39_9
    | ~ spl39_52
    | ~ spl39_375 ),
    inference(forward_demodulation,[],[f2623,f13353])).

fof(f2623,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_9 ),
    inference(avatar_component_clause,[],[f2621])).

fof(f13162,plain,
    ( spl39_375
    | ~ spl39_46
    | ~ spl39_52 ),
    inference(avatar_split_clause,[],[f4002,f3244,f3058,f13159])).

fof(f3058,plain,
    ( spl39_46
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_46])])).

fof(f4002,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_46
    | ~ spl39_52 ),
    inference(subsumption_resolution,[],[f3166,f3303])).

fof(f3303,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_52 ),
    inference(resolution,[],[f3246,f2168])).

fof(f2168,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f1878])).

fof(f1878,plain,(
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

fof(f3166,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_46 ),
    inference(resolution,[],[f3060,f2182])).

fof(f2182,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1891])).

fof(f1891,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1890])).

fof(f1890,plain,(
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

fof(f3060,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_46 ),
    inference(avatar_component_clause,[],[f3058])).

fof(f9398,plain,
    ( spl39_148
    | ~ spl39_52 ),
    inference(avatar_split_clause,[],[f3303,f3244,f9395])).

fof(f3247,plain,
    ( spl39_52
    | ~ spl39_4 ),
    inference(avatar_split_clause,[],[f2510,f2445,f3244])).

fof(f2510,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ spl39_4 ),
    inference(resolution,[],[f2447,f2218])).

fof(f2218,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f1900])).

fof(f1900,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1786])).

fof(f1786,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f3066,plain,
    ( spl39_47
    | ~ spl39_3
    | ~ spl39_4 ),
    inference(avatar_split_clause,[],[f2497,f2445,f2440,f3063])).

fof(f2497,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_3
    | ~ spl39_4 ),
    inference(subsumption_resolution,[],[f2484,f2447])).

fof(f2484,plain,
    ( ~ l1_pre_topc(sK3)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_3 ),
    inference(resolution,[],[f2442,f2178])).

fof(f2178,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f1884])).

fof(f1884,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f1883])).

fof(f1883,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1801])).

fof(f1801,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f3061,plain,
    ( spl39_46
    | ~ spl39_3
    | ~ spl39_4 ),
    inference(avatar_split_clause,[],[f2496,f2445,f2440,f3058])).

fof(f2496,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_3
    | ~ spl39_4 ),
    inference(subsumption_resolution,[],[f2483,f2447])).

fof(f2483,plain,
    ( ~ l1_pre_topc(sK3)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_3 ),
    inference(resolution,[],[f2442,f2177])).

fof(f2177,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f1884])).

fof(f2695,plain,
    ( spl39_11
    | spl39_12 ),
    inference(avatar_split_clause,[],[f2390,f2686,f2682])).

fof(f2390,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,sK2,sK3) ),
    inference(definition_unfolding,[],[f2135,f2134])).

fof(f2134,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f2031])).

fof(f2031,plain,
    ( ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | ~ v5_pre_topc(sK4,sK2,sK3) )
    & ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | v5_pre_topc(sK4,sK2,sK3) )
    & sK4 = sK5
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f2026,f2030,f2029,f2028,f2027])).

fof(f2027,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK2,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK2,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2028,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK2,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK2,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
                | ~ v5_pre_topc(X2,sK2,sK3) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
                | v5_pre_topc(X2,sK2,sK3) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f2029,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
              | ~ v5_pre_topc(X2,sK2,sK3) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
              | v5_pre_topc(X2,sK2,sK3) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
            | ~ v5_pre_topc(sK4,sK2,sK3) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
            | v5_pre_topc(sK4,sK2,sK3) )
          & sK4 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f2030,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
          | ~ v5_pre_topc(sK4,sK2,sK3) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
          | v5_pre_topc(sK4,sK2,sK3) )
        & sK4 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
        | ~ v5_pre_topc(sK4,sK2,sK3) )
      & ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
        | v5_pre_topc(sK4,sK2,sK3) )
      & sK4 = sK5
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
      & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f2026,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2025])).

fof(f2025,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f1858])).

fof(f1858,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f1857])).

fof(f1857,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1855])).

fof(f1855,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1854])).

fof(f1854,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f2135,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f2031])).

fof(f2689,plain,
    ( ~ spl39_11
    | ~ spl39_12 ),
    inference(avatar_split_clause,[],[f2389,f2686,f2682])).

fof(f2389,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v5_pre_topc(sK5,sK2,sK3) ),
    inference(definition_unfolding,[],[f2136,f2134])).

fof(f2136,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f2031])).

fof(f2680,plain,(
    spl39_10 ),
    inference(avatar_split_clause,[],[f2133,f2677])).

fof(f2133,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
    inference(cnf_transformation,[],[f2031])).

fof(f2624,plain,(
    spl39_9 ),
    inference(avatar_split_clause,[],[f2132,f2621])).

fof(f2132,plain,(
    v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(cnf_transformation,[],[f2031])).

fof(f2583,plain,(
    spl39_7 ),
    inference(avatar_split_clause,[],[f2391,f2580])).

fof(f2391,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f2130,f2134])).

fof(f2130,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f2031])).

fof(f2521,plain,(
    spl39_6 ),
    inference(avatar_split_clause,[],[f2392,f2518])).

fof(f2392,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(definition_unfolding,[],[f2129,f2134])).

fof(f2129,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f2031])).

fof(f2453,plain,(
    spl39_5 ),
    inference(avatar_split_clause,[],[f2131,f2450])).

fof(f2131,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f2031])).

fof(f2448,plain,(
    spl39_4 ),
    inference(avatar_split_clause,[],[f2127,f2445])).

fof(f2127,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f2031])).

fof(f2443,plain,(
    spl39_3 ),
    inference(avatar_split_clause,[],[f2126,f2440])).

fof(f2126,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f2031])).

fof(f2438,plain,(
    spl39_2 ),
    inference(avatar_split_clause,[],[f2125,f2435])).

fof(f2125,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f2031])).

fof(f2433,plain,(
    spl39_1 ),
    inference(avatar_split_clause,[],[f2124,f2430])).

fof(f2124,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f2031])).
%------------------------------------------------------------------------------

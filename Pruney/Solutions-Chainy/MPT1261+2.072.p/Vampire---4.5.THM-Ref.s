%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  234 ( 451 expanded)
%              Number of leaves         :   60 ( 205 expanded)
%              Depth                    :   11
%              Number of atoms          :  668 (1328 expanded)
%              Number of equality atoms :  164 ( 364 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2863,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f92,f100,f109,f117,f128,f136,f140,f161,f178,f194,f199,f210,f228,f292,f296,f371,f419,f584,f624,f628,f634,f655,f668,f694,f710,f737,f746,f805,f1226,f1482,f1499,f1507,f1562,f2533,f2537,f2839,f2849,f2862])).

fof(f2862,plain,
    ( ~ spl2_3
    | spl2_23
    | ~ spl2_58
    | ~ spl2_80
    | ~ spl2_92
    | ~ spl2_115 ),
    inference(avatar_contradiction_clause,[],[f2861])).

fof(f2861,plain,
    ( $false
    | ~ spl2_3
    | spl2_23
    | ~ spl2_58
    | ~ spl2_80
    | ~ spl2_92
    | ~ spl2_115 ),
    inference(subsumption_resolution,[],[f2860,f2854])).

fof(f2854,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | spl2_23
    | ~ spl2_80 ),
    inference(subsumption_resolution,[],[f1227,f222])).

fof(f222,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_23 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl2_23
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f1227,plain,
    ( v4_pre_topc(sK1,sK0)
    | sK1 != k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_80 ),
    inference(resolution,[],[f1225,f87])).

fof(f87,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1225,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,X0) != X0 )
    | ~ spl2_80 ),
    inference(avatar_component_clause,[],[f1224])).

fof(f1224,plain,
    ( spl2_80
  <=> ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).

fof(f2860,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_58
    | ~ spl2_92
    | ~ spl2_115 ),
    inference(forward_demodulation,[],[f2859,f736])).

fof(f736,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_58 ),
    inference(avatar_component_clause,[],[f734])).

fof(f734,plain,
    ( spl2_58
  <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f2859,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_92
    | ~ spl2_115 ),
    inference(forward_demodulation,[],[f1506,f2538])).

fof(f2538,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_115 ),
    inference(resolution,[],[f2532,f87])).

fof(f2532,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_115 ),
    inference(avatar_component_clause,[],[f2531])).

fof(f2531,plain,
    ( spl2_115
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_115])])).

fof(f1506,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_92 ),
    inference(avatar_component_clause,[],[f1504])).

fof(f1504,plain,
    ( spl2_92
  <=> k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).

fof(f2849,plain,
    ( ~ spl2_3
    | ~ spl2_59
    | ~ spl2_80
    | ~ spl2_124 ),
    inference(avatar_contradiction_clause,[],[f2848])).

fof(f2848,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_59
    | ~ spl2_80
    | ~ spl2_124 ),
    inference(subsumption_resolution,[],[f2842,f2847])).

fof(f2847,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_59
    | ~ spl2_80 ),
    inference(subsumption_resolution,[],[f43,f2846])).

fof(f2846,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_59
    | ~ spl2_80 ),
    inference(subsumption_resolution,[],[f1227,f745])).

fof(f745,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_59 ),
    inference(avatar_component_clause,[],[f743])).

fof(f743,plain,
    ( spl2_59
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f43,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f2842,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_59
    | ~ spl2_124 ),
    inference(forward_demodulation,[],[f2840,f745])).

fof(f2840,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_124 ),
    inference(resolution,[],[f2838,f87])).

fof(f2838,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) )
    | ~ spl2_124 ),
    inference(avatar_component_clause,[],[f2837])).

fof(f2837,plain,
    ( spl2_124
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_124])])).

fof(f2839,plain,
    ( spl2_124
    | ~ spl2_2
    | ~ spl2_116 ),
    inference(avatar_split_clause,[],[f2703,f2535,f80,f2837])).

fof(f80,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f2535,plain,
    ( spl2_116
  <=> ! [X1,X0] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_116])])).

fof(f2703,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) )
    | ~ spl2_2
    | ~ spl2_116 ),
    inference(resolution,[],[f2536,f82])).

fof(f82,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f2536,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) )
    | ~ spl2_116 ),
    inference(avatar_component_clause,[],[f2535])).

fof(f2537,plain,(
    spl2_116 ),
    inference(avatar_split_clause,[],[f47,f2535])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

% (24933)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f2533,plain,
    ( spl2_115
    | ~ spl2_2
    | ~ spl2_95 ),
    inference(avatar_split_clause,[],[f2049,f1560,f80,f2531])).

fof(f1560,plain,
    ( spl2_95
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).

fof(f2049,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_2
    | ~ spl2_95 ),
    inference(resolution,[],[f1561,f82])).

fof(f1561,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) )
    | ~ spl2_95 ),
    inference(avatar_component_clause,[],[f1560])).

fof(f1562,plain,(
    spl2_95 ),
    inference(avatar_split_clause,[],[f46,f1560])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f1507,plain,
    ( spl2_92
    | ~ spl2_3
    | ~ spl2_91 ),
    inference(avatar_split_clause,[],[f1500,f1497,f85,f1504])).

fof(f1497,plain,
    ( spl2_91
  <=> ! [X0] :
        ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_91])])).

fof(f1500,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_91 ),
    inference(resolution,[],[f1498,f87])).

fof(f1498,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) )
    | ~ spl2_91 ),
    inference(avatar_component_clause,[],[f1497])).

fof(f1499,plain,
    ( spl2_91
    | ~ spl2_2
    | ~ spl2_44
    | ~ spl2_88 ),
    inference(avatar_split_clause,[],[f1486,f1480,f582,f80,f1497])).

fof(f582,plain,
    ( spl2_44
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f1480,plain,
    ( spl2_88
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_tarski(k2_tarski(sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).

fof(f1486,plain,
    ( ! [X0] :
        ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_2
    | ~ spl2_44
    | ~ spl2_88 ),
    inference(subsumption_resolution,[],[f1484,f82])).

fof(f1484,plain,
    ( ! [X0] :
        ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_44
    | ~ spl2_88 ),
    inference(resolution,[],[f1481,f583])).

fof(f583,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f582])).

fof(f1481,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_tarski(k2_tarski(sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0) )
    | ~ spl2_88 ),
    inference(avatar_component_clause,[],[f1480])).

fof(f1482,plain,
    ( spl2_88
    | ~ spl2_3
    | ~ spl2_64 ),
    inference(avatar_split_clause,[],[f1312,f803,f85,f1480])).

fof(f803,plain,
    ( spl2_64
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).

fof(f1312,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_tarski(k2_tarski(sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0) )
    | ~ spl2_3
    | ~ spl2_64 ),
    inference(resolution,[],[f804,f87])).

fof(f804,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) )
    | ~ spl2_64 ),
    inference(avatar_component_clause,[],[f803])).

fof(f1226,plain,
    ( spl2_80
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f1029,f692,f80,f75,f1224])).

fof(f75,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f692,plain,
    ( spl2_54
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) != X1
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

% (24932)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
fof(f1029,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_54 ),
    inference(subsumption_resolution,[],[f1028,f82])).

fof(f1028,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_1
    | ~ spl2_54 ),
    inference(resolution,[],[f693,f77])).

fof(f77,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f693,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | k2_pre_topc(X0,X1) != X1
        | v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f692])).

fof(f805,plain,(
    spl2_64 ),
    inference(avatar_split_clause,[],[f73,f803])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f62,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f746,plain,
    ( spl2_59
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_23
    | ~ spl2_46 ),
    inference(avatar_split_clause,[],[f741,f622,f221,f85,f80,f743])).

fof(f622,plain,
    ( spl2_46
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = X1
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f741,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_23
    | ~ spl2_46 ),
    inference(subsumption_resolution,[],[f740,f82])).

fof(f740,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_23
    | ~ spl2_46 ),
    inference(subsumption_resolution,[],[f739,f87])).

fof(f739,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_23
    | ~ spl2_46 ),
    inference(resolution,[],[f223,f623])).

fof(f623,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f622])).

fof(f223,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f221])).

fof(f737,plain,
    ( spl2_58
    | ~ spl2_19
    | ~ spl2_34
    | ~ spl2_37
    | ~ spl2_56 ),
    inference(avatar_split_clause,[],[f722,f707,f417,f369,f192,f734])).

fof(f192,plain,
    ( spl2_19
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f369,plain,
    ( spl2_34
  <=> ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f417,plain,
    ( spl2_37
  <=> ! [X1,X0] : k3_tarski(k2_tarski(X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f707,plain,
    ( spl2_56
  <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f722,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_19
    | ~ spl2_34
    | ~ spl2_37
    | ~ spl2_56 ),
    inference(forward_demodulation,[],[f721,f193])).

fof(f193,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f192])).

fof(f721,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_34
    | ~ spl2_37
    | ~ spl2_56 ),
    inference(forward_demodulation,[],[f716,f370])).

fof(f370,plain,
    ( ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3)
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f369])).

fof(f716,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_37
    | ~ spl2_56 ),
    inference(superposition,[],[f418,f709])).

fof(f709,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f707])).

fof(f418,plain,
    ( ! [X0,X1] : k3_tarski(k2_tarski(X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f417])).

fof(f710,plain,
    ( spl2_56
    | ~ spl2_8
    | ~ spl2_18
    | ~ spl2_51 ),
    inference(avatar_split_clause,[],[f670,f665,f176,f107,f707])).

fof(f107,plain,
    ( spl2_8
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f176,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( k1_setfam_1(k2_tarski(X0,X1)) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f665,plain,
    ( spl2_51
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f670,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_8
    | ~ spl2_18
    | ~ spl2_51 ),
    inference(forward_demodulation,[],[f669,f108])).

fof(f108,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f669,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_18
    | ~ spl2_51 ),
    inference(resolution,[],[f667,f177])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_setfam_1(k2_tarski(X0,X1)) = X0 )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f176])).

fof(f667,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f665])).

fof(f694,plain,(
    spl2_54 ),
    inference(avatar_split_clause,[],[f49,f692])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f668,plain,
    ( spl2_51
    | ~ spl2_24
    | ~ spl2_49 ),
    inference(avatar_split_clause,[],[f662,f653,f225,f665])).

fof(f225,plain,
    ( spl2_24
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f653,plain,
    ( spl2_49
  <=> ! [X3] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f662,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_24
    | ~ spl2_49 ),
    inference(superposition,[],[f654,f227])).

fof(f227,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f225])).

fof(f654,plain,
    ( ! [X3] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X3),sK1)
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f653])).

fof(f655,plain,
    ( spl2_49
    | ~ spl2_13
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f644,f632,f138,f653])).

fof(f138,plain,
    ( spl2_13
  <=> ! [X1,X0] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f632,plain,
    ( spl2_48
  <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f644,plain,
    ( ! [X3] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X3),sK1)
    | ~ spl2_13
    | ~ spl2_48 ),
    inference(superposition,[],[f139,f633])).

fof(f633,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f632])).

fof(f139,plain,
    ( ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f138])).

fof(f634,plain,
    ( spl2_48
    | ~ spl2_3
    | ~ spl2_47 ),
    inference(avatar_split_clause,[],[f629,f626,f85,f632])).

fof(f626,plain,
    ( spl2_47
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f629,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))
    | ~ spl2_3
    | ~ spl2_47 ),
    inference(resolution,[],[f627,f87])).

fof(f627,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) )
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f626])).

fof(f628,plain,(
    spl2_47 ),
    inference(avatar_split_clause,[],[f72,f626])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f61,f63])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f58,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f624,plain,(
    spl2_46 ),
    inference(avatar_split_clause,[],[f48,f622])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f584,plain,(
    spl2_44 ),
    inference(avatar_split_clause,[],[f60,f582])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f419,plain,
    ( spl2_37
    | ~ spl2_8
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f297,f290,f107,f417])).

fof(f290,plain,
    ( spl2_30
  <=> ! [X1,X0] : k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f297,plain,
    ( ! [X0,X1] : k3_tarski(k2_tarski(X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))))
    | ~ spl2_8
    | ~ spl2_30 ),
    inference(superposition,[],[f291,f108])).

fof(f291,plain,
    ( ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f290])).

fof(f371,plain,
    ( spl2_34
    | ~ spl2_19
    | ~ spl2_21
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f354,f294,f208,f192,f369])).

fof(f208,plain,
    ( spl2_21
  <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f294,plain,
    ( spl2_31
  <=> ! [X1,X0] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f354,plain,
    ( ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3)
    | ~ spl2_19
    | ~ spl2_21
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f346,f193])).

fof(f346,plain,
    ( ! [X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X3,k1_xboole_0))
    | ~ spl2_21
    | ~ spl2_31 ),
    inference(superposition,[],[f295,f209])).

fof(f209,plain,
    ( ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f208])).

fof(f295,plain,
    ( ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f294])).

fof(f296,plain,
    ( spl2_31
    | ~ spl2_8
    | ~ spl2_13
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f188,f176,f138,f107,f294])).

fof(f188,plain,
    ( ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
    | ~ spl2_8
    | ~ spl2_13
    | ~ spl2_18 ),
    inference(backward_demodulation,[],[f70,f187])).

fof(f187,plain,
    ( ! [X6,X7] : k5_xboole_0(X6,k1_setfam_1(k2_tarski(X6,X7))) = k1_setfam_1(k2_tarski(X6,k5_xboole_0(X6,k1_setfam_1(k2_tarski(X6,X7)))))
    | ~ spl2_8
    | ~ spl2_13
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f183,f108])).

fof(f183,plain,
    ( ! [X6,X7] : k5_xboole_0(X6,k1_setfam_1(k2_tarski(X6,X7))) = k1_setfam_1(k2_tarski(k5_xboole_0(X6,k1_setfam_1(k2_tarski(X6,X7))),X6))
    | ~ spl2_13
    | ~ spl2_18 ),
    inference(resolution,[],[f177,f139])).

fof(f70,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f57,f55,f63,f63])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f292,plain,(
    spl2_30 ),
    inference(avatar_split_clause,[],[f69,f290])).

fof(f69,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(definition_unfolding,[],[f56,f54,f63])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f228,plain,
    ( spl2_23
    | spl2_24 ),
    inference(avatar_split_clause,[],[f42,f225,f221])).

fof(f42,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f210,plain,
    ( spl2_21
    | ~ spl2_8
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f200,f197,f107,f208])).

fof(f197,plain,
    ( spl2_20
  <=> ! [X5] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f200,plain,
    ( ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))
    | ~ spl2_8
    | ~ spl2_20 ),
    inference(superposition,[],[f198,f108])).

fof(f198,plain,
    ( ! [X5] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X5))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f197])).

fof(f199,plain,
    ( spl2_20
    | ~ spl2_11
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f182,f176,f126,f197])).

fof(f126,plain,
    ( spl2_11
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f182,plain,
    ( ! [X5] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X5))
    | ~ spl2_11
    | ~ spl2_18 ),
    inference(resolution,[],[f177,f127])).

fof(f127,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f194,plain,
    ( spl2_19
    | ~ spl2_11
    | ~ spl2_16
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f186,f176,f159,f126,f192])).

fof(f159,plain,
    ( spl2_16
  <=> ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f186,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_11
    | ~ spl2_16
    | ~ spl2_18 ),
    inference(backward_demodulation,[],[f160,f182])).

fof(f160,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = X0
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f159])).

fof(f178,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f71,f176])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f55])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f161,plain,
    ( spl2_16
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f141,f134,f107,f159])).

fof(f134,plain,
    ( spl2_12
  <=> ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f141,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = X0
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(superposition,[],[f135,f108])).

fof(f135,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f140,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f68,f138])).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f52,f63])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f136,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f65,f134])).

fof(f65,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f45,f63])).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f128,plain,
    ( spl2_11
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f124,f115,f98,f126])).

fof(f98,plain,
    ( spl2_6
  <=> ! [X1,X0] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f115,plain,
    ( spl2_9
  <=> ! [X0] : k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f124,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(superposition,[],[f99,f116])).

fof(f116,plain,
    ( ! [X0] : k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f99,plain,
    ( ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f117,plain,
    ( spl2_9
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f110,f107,f90,f115])).

fof(f90,plain,
    ( spl2_4
  <=> ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f110,plain,
    ( ! [X0] : k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(superposition,[],[f91,f108])).

fof(f91,plain,
    ( ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f109,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f53,f107])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f100,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f67,f98])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f51,f54])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f92,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f64,f90])).

fof(f64,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f44,f54])).

fof(f44,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f88,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f41,f85])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f83,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f40,f80])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f39,f75])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (24928)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (24924)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (24925)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (24921)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (24929)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (24928)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f2863,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f78,f83,f88,f92,f100,f109,f117,f128,f136,f140,f161,f178,f194,f199,f210,f228,f292,f296,f371,f419,f584,f624,f628,f634,f655,f668,f694,f710,f737,f746,f805,f1226,f1482,f1499,f1507,f1562,f2533,f2537,f2839,f2849,f2862])).
% 0.20/0.47  fof(f2862,plain,(
% 0.20/0.47    ~spl2_3 | spl2_23 | ~spl2_58 | ~spl2_80 | ~spl2_92 | ~spl2_115),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f2861])).
% 0.20/0.47  fof(f2861,plain,(
% 0.20/0.47    $false | (~spl2_3 | spl2_23 | ~spl2_58 | ~spl2_80 | ~spl2_92 | ~spl2_115)),
% 0.20/0.47    inference(subsumption_resolution,[],[f2860,f2854])).
% 0.20/0.47  fof(f2854,plain,(
% 0.20/0.47    sK1 != k2_pre_topc(sK0,sK1) | (~spl2_3 | spl2_23 | ~spl2_80)),
% 0.20/0.47    inference(subsumption_resolution,[],[f1227,f222])).
% 0.20/0.47  fof(f222,plain,(
% 0.20/0.47    ~v4_pre_topc(sK1,sK0) | spl2_23),
% 0.20/0.47    inference(avatar_component_clause,[],[f221])).
% 0.20/0.47  fof(f221,plain,(
% 0.20/0.47    spl2_23 <=> v4_pre_topc(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.20/0.47  fof(f1227,plain,(
% 0.20/0.47    v4_pre_topc(sK1,sK0) | sK1 != k2_pre_topc(sK0,sK1) | (~spl2_3 | ~spl2_80)),
% 0.20/0.47    inference(resolution,[],[f1225,f87])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f85])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.47  fof(f1225,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) != X0) ) | ~spl2_80),
% 0.20/0.47    inference(avatar_component_clause,[],[f1224])).
% 0.20/0.47  fof(f1224,plain,(
% 0.20/0.47    spl2_80 <=> ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).
% 0.20/0.47  fof(f2860,plain,(
% 0.20/0.47    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_3 | ~spl2_58 | ~spl2_92 | ~spl2_115)),
% 0.20/0.47    inference(forward_demodulation,[],[f2859,f736])).
% 0.20/0.47  fof(f736,plain,(
% 0.20/0.47    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_58),
% 0.20/0.47    inference(avatar_component_clause,[],[f734])).
% 0.20/0.47  fof(f734,plain,(
% 0.20/0.47    spl2_58 <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 0.20/0.47  fof(f2859,plain,(
% 0.20/0.47    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) | (~spl2_3 | ~spl2_92 | ~spl2_115)),
% 0.20/0.47    inference(forward_demodulation,[],[f1506,f2538])).
% 0.20/0.47  fof(f2538,plain,(
% 0.20/0.47    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_115)),
% 0.20/0.47    inference(resolution,[],[f2532,f87])).
% 0.20/0.47  fof(f2532,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | ~spl2_115),
% 0.20/0.47    inference(avatar_component_clause,[],[f2531])).
% 0.20/0.47  fof(f2531,plain,(
% 0.20/0.47    spl2_115 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_115])])).
% 0.20/0.47  fof(f1506,plain,(
% 0.20/0.47    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_92),
% 0.20/0.47    inference(avatar_component_clause,[],[f1504])).
% 0.20/0.47  fof(f1504,plain,(
% 0.20/0.47    spl2_92 <=> k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).
% 0.20/0.47  fof(f2849,plain,(
% 0.20/0.47    ~spl2_3 | ~spl2_59 | ~spl2_80 | ~spl2_124),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f2848])).
% 0.20/0.47  fof(f2848,plain,(
% 0.20/0.47    $false | (~spl2_3 | ~spl2_59 | ~spl2_80 | ~spl2_124)),
% 0.20/0.47    inference(subsumption_resolution,[],[f2842,f2847])).
% 0.20/0.47  fof(f2847,plain,(
% 0.20/0.47    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_59 | ~spl2_80)),
% 0.20/0.47    inference(subsumption_resolution,[],[f43,f2846])).
% 0.20/0.47  fof(f2846,plain,(
% 0.20/0.47    v4_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_59 | ~spl2_80)),
% 0.20/0.47    inference(subsumption_resolution,[],[f1227,f745])).
% 0.20/0.47  fof(f745,plain,(
% 0.20/0.47    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_59),
% 0.20/0.47    inference(avatar_component_clause,[],[f743])).
% 0.20/0.47  fof(f743,plain,(
% 0.20/0.47    spl2_59 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.20/0.47    inference(negated_conjecture,[],[f19])).
% 0.20/0.47  fof(f19,conjecture,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 0.20/0.47  fof(f2842,plain,(
% 0.20/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_59 | ~spl2_124)),
% 0.20/0.47    inference(forward_demodulation,[],[f2840,f745])).
% 0.20/0.47  fof(f2840,plain,(
% 0.20/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_124)),
% 0.20/0.47    inference(resolution,[],[f2838,f87])).
% 0.20/0.47  fof(f2838,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) ) | ~spl2_124),
% 0.20/0.47    inference(avatar_component_clause,[],[f2837])).
% 0.20/0.47  fof(f2837,plain,(
% 0.20/0.47    spl2_124 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_124])])).
% 0.20/0.47  fof(f2839,plain,(
% 0.20/0.47    spl2_124 | ~spl2_2 | ~spl2_116),
% 0.20/0.47    inference(avatar_split_clause,[],[f2703,f2535,f80,f2837])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    spl2_2 <=> l1_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.47  fof(f2535,plain,(
% 0.20/0.47    spl2_116 <=> ! [X1,X0] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_116])])).
% 0.20/0.47  fof(f2703,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) ) | (~spl2_2 | ~spl2_116)),
% 0.20/0.47    inference(resolution,[],[f2536,f82])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    l1_pre_topc(sK0) | ~spl2_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f80])).
% 0.20/0.47  fof(f2536,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) ) | ~spl2_116),
% 0.20/0.47    inference(avatar_component_clause,[],[f2535])).
% 0.20/0.47  fof(f2537,plain,(
% 0.20/0.47    spl2_116),
% 0.20/0.47    inference(avatar_split_clause,[],[f47,f2535])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.20/0.47  % (24933)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  fof(f2533,plain,(
% 0.20/0.47    spl2_115 | ~spl2_2 | ~spl2_95),
% 0.20/0.47    inference(avatar_split_clause,[],[f2049,f1560,f80,f2531])).
% 0.20/0.47  fof(f1560,plain,(
% 0.20/0.47    spl2_95 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).
% 0.20/0.47  fof(f2049,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | (~spl2_2 | ~spl2_95)),
% 0.20/0.47    inference(resolution,[],[f1561,f82])).
% 0.20/0.47  fof(f1561,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) ) | ~spl2_95),
% 0.20/0.47    inference(avatar_component_clause,[],[f1560])).
% 0.20/0.47  fof(f1562,plain,(
% 0.20/0.47    spl2_95),
% 0.20/0.47    inference(avatar_split_clause,[],[f46,f1560])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.20/0.47  fof(f1507,plain,(
% 0.20/0.47    spl2_92 | ~spl2_3 | ~spl2_91),
% 0.20/0.47    inference(avatar_split_clause,[],[f1500,f1497,f85,f1504])).
% 0.20/0.47  fof(f1497,plain,(
% 0.20/0.47    spl2_91 <=> ! [X0] : (k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_91])])).
% 0.20/0.47  fof(f1500,plain,(
% 0.20/0.47    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_91)),
% 0.20/0.47    inference(resolution,[],[f1498,f87])).
% 0.20/0.47  fof(f1498,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0))) ) | ~spl2_91),
% 0.20/0.47    inference(avatar_component_clause,[],[f1497])).
% 0.20/0.47  fof(f1499,plain,(
% 0.20/0.47    spl2_91 | ~spl2_2 | ~spl2_44 | ~spl2_88),
% 0.20/0.47    inference(avatar_split_clause,[],[f1486,f1480,f582,f80,f1497])).
% 0.20/0.47  fof(f582,plain,(
% 0.20/0.47    spl2_44 <=> ! [X1,X0] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 0.20/0.47  fof(f1480,plain,(
% 0.20/0.47    spl2_88 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_tarski(k2_tarski(sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).
% 0.20/0.47  fof(f1486,plain,(
% 0.20/0.47    ( ! [X0] : (k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_2 | ~spl2_44 | ~spl2_88)),
% 0.20/0.47    inference(subsumption_resolution,[],[f1484,f82])).
% 0.20/0.47  fof(f1484,plain,(
% 0.20/0.47    ( ! [X0] : (k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | (~spl2_44 | ~spl2_88)),
% 0.20/0.47    inference(resolution,[],[f1481,f583])).
% 0.20/0.47  fof(f583,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_44),
% 0.20/0.47    inference(avatar_component_clause,[],[f582])).
% 0.20/0.47  fof(f1481,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_tarski(k2_tarski(sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_88),
% 0.20/0.47    inference(avatar_component_clause,[],[f1480])).
% 0.20/0.47  fof(f1482,plain,(
% 0.20/0.47    spl2_88 | ~spl2_3 | ~spl2_64),
% 0.20/0.47    inference(avatar_split_clause,[],[f1312,f803,f85,f1480])).
% 0.20/0.47  fof(f803,plain,(
% 0.20/0.47    spl2_64 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).
% 0.20/0.47  fof(f1312,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_tarski(k2_tarski(sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)) ) | (~spl2_3 | ~spl2_64)),
% 0.20/0.47    inference(resolution,[],[f804,f87])).
% 0.20/0.47  fof(f804,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))) ) | ~spl2_64),
% 0.20/0.47    inference(avatar_component_clause,[],[f803])).
% 0.20/0.47  fof(f1226,plain,(
% 0.20/0.47    spl2_80 | ~spl2_1 | ~spl2_2 | ~spl2_54),
% 0.20/0.47    inference(avatar_split_clause,[],[f1029,f692,f80,f75,f1224])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    spl2_1 <=> v2_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.47  fof(f692,plain,(
% 0.20/0.47    spl2_54 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 0.20/0.47  % (24932)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  fof(f1029,plain,(
% 0.20/0.47    ( ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_1 | ~spl2_2 | ~spl2_54)),
% 0.20/0.47    inference(subsumption_resolution,[],[f1028,f82])).
% 0.20/0.47  fof(f1028,plain,(
% 0.20/0.47    ( ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | (~spl2_1 | ~spl2_54)),
% 0.20/0.47    inference(resolution,[],[f693,f77])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    v2_pre_topc(sK0) | ~spl2_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f75])).
% 0.20/0.47  fof(f693,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v2_pre_topc(X0) | k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_54),
% 0.20/0.47    inference(avatar_component_clause,[],[f692])).
% 0.20/0.47  fof(f805,plain,(
% 0.20/0.47    spl2_64),
% 0.20/0.47    inference(avatar_split_clause,[],[f73,f803])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f62,f54])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(flattening,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.47  fof(f746,plain,(
% 0.20/0.47    spl2_59 | ~spl2_2 | ~spl2_3 | ~spl2_23 | ~spl2_46),
% 0.20/0.47    inference(avatar_split_clause,[],[f741,f622,f221,f85,f80,f743])).
% 0.20/0.47  fof(f622,plain,(
% 0.20/0.47    spl2_46 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 0.20/0.47  fof(f741,plain,(
% 0.20/0.47    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_3 | ~spl2_23 | ~spl2_46)),
% 0.20/0.47    inference(subsumption_resolution,[],[f740,f82])).
% 0.20/0.47  fof(f740,plain,(
% 0.20/0.47    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_23 | ~spl2_46)),
% 0.20/0.47    inference(subsumption_resolution,[],[f739,f87])).
% 0.20/0.47  fof(f739,plain,(
% 0.20/0.47    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_23 | ~spl2_46)),
% 0.20/0.47    inference(resolution,[],[f223,f623])).
% 0.20/0.47  fof(f623,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_46),
% 0.20/0.47    inference(avatar_component_clause,[],[f622])).
% 0.20/0.47  fof(f223,plain,(
% 0.20/0.47    v4_pre_topc(sK1,sK0) | ~spl2_23),
% 0.20/0.47    inference(avatar_component_clause,[],[f221])).
% 0.20/0.47  fof(f737,plain,(
% 0.20/0.47    spl2_58 | ~spl2_19 | ~spl2_34 | ~spl2_37 | ~spl2_56),
% 0.20/0.47    inference(avatar_split_clause,[],[f722,f707,f417,f369,f192,f734])).
% 0.20/0.47  fof(f192,plain,(
% 0.20/0.47    spl2_19 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.47  fof(f369,plain,(
% 0.20/0.47    spl2_34 <=> ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.20/0.47  fof(f417,plain,(
% 0.20/0.47    spl2_37 <=> ! [X1,X0] : k3_tarski(k2_tarski(X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.20/0.47  fof(f707,plain,(
% 0.20/0.47    spl2_56 <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 0.20/0.47  fof(f722,plain,(
% 0.20/0.47    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_19 | ~spl2_34 | ~spl2_37 | ~spl2_56)),
% 0.20/0.47    inference(forward_demodulation,[],[f721,f193])).
% 0.20/0.47  fof(f193,plain,(
% 0.20/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f192])).
% 0.20/0.47  fof(f721,plain,(
% 0.20/0.47    k5_xboole_0(sK1,k1_xboole_0) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_34 | ~spl2_37 | ~spl2_56)),
% 0.20/0.47    inference(forward_demodulation,[],[f716,f370])).
% 0.20/0.47  fof(f370,plain,(
% 0.20/0.47    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) ) | ~spl2_34),
% 0.20/0.47    inference(avatar_component_clause,[],[f369])).
% 0.20/0.47  fof(f716,plain,(
% 0.20/0.47    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) | (~spl2_37 | ~spl2_56)),
% 0.20/0.47    inference(superposition,[],[f418,f709])).
% 0.20/0.47  fof(f709,plain,(
% 0.20/0.47    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_56),
% 0.20/0.47    inference(avatar_component_clause,[],[f707])).
% 0.20/0.47  fof(f418,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_tarski(k2_tarski(X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))))) ) | ~spl2_37),
% 0.20/0.47    inference(avatar_component_clause,[],[f417])).
% 0.20/0.47  fof(f710,plain,(
% 0.20/0.47    spl2_56 | ~spl2_8 | ~spl2_18 | ~spl2_51),
% 0.20/0.47    inference(avatar_split_clause,[],[f670,f665,f176,f107,f707])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    spl2_8 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    spl2_18 <=> ! [X1,X0] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.47  fof(f665,plain,(
% 0.20/0.47    spl2_51 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 0.20/0.47  fof(f670,plain,(
% 0.20/0.47    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_8 | ~spl2_18 | ~spl2_51)),
% 0.20/0.47    inference(forward_demodulation,[],[f669,f108])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f107])).
% 0.20/0.47  fof(f669,plain,(
% 0.20/0.47    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) | (~spl2_18 | ~spl2_51)),
% 0.20/0.47    inference(resolution,[],[f667,f177])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) ) | ~spl2_18),
% 0.20/0.47    inference(avatar_component_clause,[],[f176])).
% 0.20/0.47  fof(f667,plain,(
% 0.20/0.47    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_51),
% 0.20/0.47    inference(avatar_component_clause,[],[f665])).
% 0.20/0.47  fof(f694,plain,(
% 0.20/0.47    spl2_54),
% 0.20/0.47    inference(avatar_split_clause,[],[f49,f692])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.20/0.47  fof(f668,plain,(
% 0.20/0.47    spl2_51 | ~spl2_24 | ~spl2_49),
% 0.20/0.47    inference(avatar_split_clause,[],[f662,f653,f225,f665])).
% 0.20/0.47  fof(f225,plain,(
% 0.20/0.47    spl2_24 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.20/0.47  fof(f653,plain,(
% 0.20/0.47    spl2_49 <=> ! [X3] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X3),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 0.20/0.47  fof(f662,plain,(
% 0.20/0.47    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_24 | ~spl2_49)),
% 0.20/0.47    inference(superposition,[],[f654,f227])).
% 0.20/0.47  fof(f227,plain,(
% 0.20/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_24),
% 0.20/0.47    inference(avatar_component_clause,[],[f225])).
% 0.20/0.47  fof(f654,plain,(
% 0.20/0.47    ( ! [X3] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X3),sK1)) ) | ~spl2_49),
% 0.20/0.47    inference(avatar_component_clause,[],[f653])).
% 0.20/0.47  fof(f655,plain,(
% 0.20/0.47    spl2_49 | ~spl2_13 | ~spl2_48),
% 0.20/0.47    inference(avatar_split_clause,[],[f644,f632,f138,f653])).
% 0.20/0.47  fof(f138,plain,(
% 0.20/0.47    spl2_13 <=> ! [X1,X0] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.47  fof(f632,plain,(
% 0.20/0.47    spl2_48 <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 0.20/0.47  fof(f644,plain,(
% 0.20/0.47    ( ! [X3] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X3),sK1)) ) | (~spl2_13 | ~spl2_48)),
% 0.20/0.47    inference(superposition,[],[f139,f633])).
% 0.20/0.47  fof(f633,plain,(
% 0.20/0.47    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) ) | ~spl2_48),
% 0.20/0.47    inference(avatar_component_clause,[],[f632])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) ) | ~spl2_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f138])).
% 0.20/0.47  fof(f634,plain,(
% 0.20/0.47    spl2_48 | ~spl2_3 | ~spl2_47),
% 0.20/0.47    inference(avatar_split_clause,[],[f629,f626,f85,f632])).
% 0.20/0.47  fof(f626,plain,(
% 0.20/0.47    spl2_47 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 0.20/0.47  fof(f629,plain,(
% 0.20/0.47    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) ) | (~spl2_3 | ~spl2_47)),
% 0.20/0.47    inference(resolution,[],[f627,f87])).
% 0.20/0.47  fof(f627,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) ) | ~spl2_47),
% 0.20/0.47    inference(avatar_component_clause,[],[f626])).
% 0.20/0.47  fof(f628,plain,(
% 0.20/0.47    spl2_47),
% 0.20/0.47    inference(avatar_split_clause,[],[f72,f626])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f61,f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f58,f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.20/0.47  fof(f624,plain,(
% 0.20/0.47    spl2_46),
% 0.20/0.47    inference(avatar_split_clause,[],[f48,f622])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f584,plain,(
% 0.20/0.47    spl2_44),
% 0.20/0.47    inference(avatar_split_clause,[],[f60,f582])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,axiom,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.20/0.47  fof(f419,plain,(
% 0.20/0.47    spl2_37 | ~spl2_8 | ~spl2_30),
% 0.20/0.47    inference(avatar_split_clause,[],[f297,f290,f107,f417])).
% 0.20/0.47  fof(f290,plain,(
% 0.20/0.47    spl2_30 <=> ! [X1,X0] : k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.20/0.47  fof(f297,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_tarski(k2_tarski(X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))))) ) | (~spl2_8 | ~spl2_30)),
% 0.20/0.47    inference(superposition,[],[f291,f108])).
% 0.20/0.47  fof(f291,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) ) | ~spl2_30),
% 0.20/0.47    inference(avatar_component_clause,[],[f290])).
% 0.20/0.47  fof(f371,plain,(
% 0.20/0.47    spl2_34 | ~spl2_19 | ~spl2_21 | ~spl2_31),
% 0.20/0.47    inference(avatar_split_clause,[],[f354,f294,f208,f192,f369])).
% 0.20/0.47  fof(f208,plain,(
% 0.20/0.47    spl2_21 <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.20/0.47  fof(f294,plain,(
% 0.20/0.47    spl2_31 <=> ! [X1,X0] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.20/0.47  fof(f354,plain,(
% 0.20/0.47    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) ) | (~spl2_19 | ~spl2_21 | ~spl2_31)),
% 0.20/0.47    inference(forward_demodulation,[],[f346,f193])).
% 0.20/0.47  fof(f346,plain,(
% 0.20/0.47    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X3,k1_xboole_0))) ) | (~spl2_21 | ~spl2_31)),
% 0.20/0.47    inference(superposition,[],[f295,f209])).
% 0.20/0.47  fof(f209,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) ) | ~spl2_21),
% 0.20/0.47    inference(avatar_component_clause,[],[f208])).
% 0.20/0.47  fof(f295,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) ) | ~spl2_31),
% 0.20/0.47    inference(avatar_component_clause,[],[f294])).
% 0.20/0.47  fof(f296,plain,(
% 0.20/0.47    spl2_31 | ~spl2_8 | ~spl2_13 | ~spl2_18),
% 0.20/0.47    inference(avatar_split_clause,[],[f188,f176,f138,f107,f294])).
% 0.20/0.47  fof(f188,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) ) | (~spl2_8 | ~spl2_13 | ~spl2_18)),
% 0.20/0.47    inference(backward_demodulation,[],[f70,f187])).
% 0.20/0.47  fof(f187,plain,(
% 0.20/0.47    ( ! [X6,X7] : (k5_xboole_0(X6,k1_setfam_1(k2_tarski(X6,X7))) = k1_setfam_1(k2_tarski(X6,k5_xboole_0(X6,k1_setfam_1(k2_tarski(X6,X7)))))) ) | (~spl2_8 | ~spl2_13 | ~spl2_18)),
% 0.20/0.47    inference(forward_demodulation,[],[f183,f108])).
% 0.20/0.47  fof(f183,plain,(
% 0.20/0.47    ( ! [X6,X7] : (k5_xboole_0(X6,k1_setfam_1(k2_tarski(X6,X7))) = k1_setfam_1(k2_tarski(k5_xboole_0(X6,k1_setfam_1(k2_tarski(X6,X7))),X6))) ) | (~spl2_13 | ~spl2_18)),
% 0.20/0.47    inference(resolution,[],[f177,f139])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f57,f55,f63,f63])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.47  fof(f292,plain,(
% 0.20/0.47    spl2_30),
% 0.20/0.47    inference(avatar_split_clause,[],[f69,f290])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f56,f54,f63])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.47  fof(f228,plain,(
% 0.20/0.47    spl2_23 | spl2_24),
% 0.20/0.47    inference(avatar_split_clause,[],[f42,f225,f221])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f38])).
% 0.20/0.47  fof(f210,plain,(
% 0.20/0.47    spl2_21 | ~spl2_8 | ~spl2_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f200,f197,f107,f208])).
% 0.20/0.47  fof(f197,plain,(
% 0.20/0.47    spl2_20 <=> ! [X5] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X5))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.20/0.47  fof(f200,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) ) | (~spl2_8 | ~spl2_20)),
% 0.20/0.47    inference(superposition,[],[f198,f108])).
% 0.20/0.47  fof(f198,plain,(
% 0.20/0.47    ( ! [X5] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X5))) ) | ~spl2_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f197])).
% 0.20/0.47  fof(f199,plain,(
% 0.20/0.47    spl2_20 | ~spl2_11 | ~spl2_18),
% 0.20/0.47    inference(avatar_split_clause,[],[f182,f176,f126,f197])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    spl2_11 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.47  fof(f182,plain,(
% 0.20/0.47    ( ! [X5] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X5))) ) | (~spl2_11 | ~spl2_18)),
% 0.20/0.47    inference(resolution,[],[f177,f127])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl2_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f126])).
% 0.20/0.47  fof(f194,plain,(
% 0.20/0.47    spl2_19 | ~spl2_11 | ~spl2_16 | ~spl2_18),
% 0.20/0.47    inference(avatar_split_clause,[],[f186,f176,f159,f126,f192])).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    spl2_16 <=> ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = X0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl2_11 | ~spl2_16 | ~spl2_18)),
% 0.20/0.47    inference(backward_demodulation,[],[f160,f182])).
% 0.20/0.47  fof(f160,plain,(
% 0.20/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = X0) ) | ~spl2_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f159])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    spl2_18),
% 0.20/0.47    inference(avatar_split_clause,[],[f71,f176])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f59,f55])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    spl2_16 | ~spl2_8 | ~spl2_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f141,f134,f107,f159])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    spl2_12 <=> ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = X0) ) | (~spl2_8 | ~spl2_12)),
% 0.20/0.48    inference(superposition,[],[f135,f108])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) ) | ~spl2_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f134])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    spl2_13),
% 0.20/0.48    inference(avatar_split_clause,[],[f68,f138])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f52,f63])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    spl2_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f65,f134])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 0.20/0.48    inference(definition_unfolding,[],[f45,f63])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    spl2_11 | ~spl2_6 | ~spl2_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f124,f115,f98,f126])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    spl2_6 <=> ! [X1,X0] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    spl2_9 <=> ! [X0] : k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl2_6 | ~spl2_9)),
% 0.20/0.48    inference(superposition,[],[f99,f116])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    ( ! [X0] : (k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0) ) | ~spl2_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f115])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ) | ~spl2_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f98])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    spl2_9 | ~spl2_4 | ~spl2_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f110,f107,f90,f115])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    spl2_4 <=> ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    ( ! [X0] : (k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0) ) | (~spl2_4 | ~spl2_8)),
% 0.20/0.48    inference(superposition,[],[f91,f108])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) ) | ~spl2_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f90])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    spl2_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f53,f107])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    spl2_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f67,f98])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f51,f54])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    spl2_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f64,f90])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 0.20/0.48    inference(definition_unfolding,[],[f44,f54])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    spl2_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f41,f85])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    spl2_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f40,f80])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    l1_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    spl2_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f39,f75])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    v2_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (24928)------------------------------
% 0.20/0.48  % (24928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (24928)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (24928)Memory used [KB]: 7803
% 0.20/0.48  % (24928)Time elapsed: 0.058 s
% 0.20/0.48  % (24928)------------------------------
% 0.20/0.48  % (24928)------------------------------
% 0.20/0.48  % (24926)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (24920)Success in time 0.125 s
%------------------------------------------------------------------------------

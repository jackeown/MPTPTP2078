%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  230 ( 433 expanded)
%              Number of leaves         :   56 ( 201 expanded)
%              Depth                    :   11
%              Number of atoms          :  735 (1415 expanded)
%              Number of equality atoms :  125 ( 276 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3240,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f94,f98,f118,f122,f126,f162,f199,f213,f235,f239,f244,f257,f273,f328,f371,f403,f418,f436,f442,f445,f469,f517,f563,f571,f587,f639,f845,f864,f887,f1127,f1239,f1350,f1375,f1566,f1657,f1769,f1797,f2416,f2772,f2903,f3218,f3236])).

fof(f3236,plain,
    ( ~ spl2_68
    | ~ spl2_129
    | spl2_145
    | ~ spl2_147
    | ~ spl2_193 ),
    inference(avatar_contradiction_clause,[],[f3235])).

fof(f3235,plain,
    ( $false
    | ~ spl2_68
    | ~ spl2_129
    | spl2_145
    | ~ spl2_147
    | ~ spl2_193 ),
    inference(subsumption_resolution,[],[f3234,f1655])).

fof(f1655,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl2_145 ),
    inference(avatar_component_clause,[],[f1654])).

fof(f1654,plain,
    ( spl2_145
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_145])])).

fof(f3234,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_68
    | ~ spl2_129
    | ~ spl2_147
    | ~ spl2_193 ),
    inference(forward_demodulation,[],[f3232,f1796])).

fof(f1796,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_147 ),
    inference(avatar_component_clause,[],[f1794])).

fof(f1794,plain,
    ( spl2_147
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_147])])).

fof(f3232,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_68
    | ~ spl2_129
    | ~ spl2_193 ),
    inference(backward_demodulation,[],[f1238,f3228])).

fof(f3228,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_68
    | ~ spl2_193 ),
    inference(superposition,[],[f3217,f586])).

fof(f586,plain,
    ( ! [X1] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X1) = k4_xboole_0(k2_pre_topc(sK0,sK1),X1)
    | ~ spl2_68 ),
    inference(avatar_component_clause,[],[f585])).

fof(f585,plain,
    ( spl2_68
  <=> ! [X1] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X1) = k4_xboole_0(k2_pre_topc(sK0,sK1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).

fof(f3217,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_193 ),
    inference(avatar_component_clause,[],[f3215])).

fof(f3215,plain,
    ( spl2_193
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_193])])).

fof(f1238,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_129 ),
    inference(avatar_component_clause,[],[f1236])).

fof(f1236,plain,
    ( spl2_129
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_129])])).

fof(f3218,plain,
    ( spl2_193
    | ~ spl2_5
    | ~ spl2_178 ),
    inference(avatar_split_clause,[],[f2900,f2770,f91,f3215])).

fof(f91,plain,
    ( spl2_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f2770,plain,
    ( spl2_178
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_178])])).

fof(f2900,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_178 ),
    inference(resolution,[],[f2771,f93])).

fof(f93,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f2771,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) )
    | ~ spl2_178 ),
    inference(avatar_component_clause,[],[f2770])).

fof(f2903,plain,
    ( ~ spl2_5
    | spl2_25
    | ~ spl2_145
    | ~ spl2_178 ),
    inference(avatar_contradiction_clause,[],[f2902])).

fof(f2902,plain,
    ( $false
    | ~ spl2_5
    | spl2_25
    | ~ spl2_145
    | ~ spl2_178 ),
    inference(subsumption_resolution,[],[f2901,f211])).

fof(f211,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl2_25 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl2_25
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f2901,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_5
    | ~ spl2_145
    | ~ spl2_178 ),
    inference(forward_demodulation,[],[f2900,f1656])).

fof(f1656,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_145 ),
    inference(avatar_component_clause,[],[f1654])).

fof(f2772,plain,
    ( spl2_178
    | ~ spl2_2
    | ~ spl2_117 ),
    inference(avatar_split_clause,[],[f1221,f1125,f78,f2770])).

fof(f78,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1125,plain,
    ( spl2_117
  <=> ! [X1,X0] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_117])])).

fof(f1221,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) )
    | ~ spl2_2
    | ~ spl2_117 ),
    inference(resolution,[],[f1126,f80])).

fof(f80,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f1126,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) )
    | ~ spl2_117 ),
    inference(avatar_component_clause,[],[f1125])).

fof(f2416,plain,
    ( ~ spl2_73
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_34
    | ~ spl2_68
    | ~ spl2_145 ),
    inference(avatar_split_clause,[],[f2380,f1654,f585,f271,f91,f78,f73,f611])).

fof(f611,plain,
    ( spl2_73
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).

fof(f73,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f271,plain,
    ( spl2_34
  <=> ! [X1,X0] :
        ( v3_pre_topc(k1_tops_1(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f2380,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_34
    | ~ spl2_68
    | ~ spl2_145 ),
    inference(subsumption_resolution,[],[f602,f2379])).

fof(f2379,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_34
    | ~ spl2_145 ),
    inference(subsumption_resolution,[],[f2378,f75])).

fof(f75,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f2378,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_34
    | ~ spl2_145 ),
    inference(subsumption_resolution,[],[f2377,f80])).

fof(f2377,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_5
    | ~ spl2_34
    | ~ spl2_145 ),
    inference(subsumption_resolution,[],[f2371,f93])).

fof(f2371,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_34
    | ~ spl2_145 ),
    inference(superposition,[],[f272,f1656])).

fof(f272,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(k1_tops_1(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f271])).

fof(f602,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_68 ),
    inference(forward_demodulation,[],[f50,f586])).

fof(f50,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
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
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

% (12500)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
fof(f1797,plain,
    ( spl2_147
    | ~ spl2_25
    | ~ spl2_57
    | ~ spl2_68 ),
    inference(avatar_split_clause,[],[f1767,f585,f466,f210,f1794])).

fof(f466,plain,
    ( spl2_57
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f1767,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_25
    | ~ spl2_57
    | ~ spl2_68 ),
    inference(backward_demodulation,[],[f468,f1760])).

fof(f1760,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_25
    | ~ spl2_68 ),
    inference(superposition,[],[f586,f212])).

fof(f212,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f210])).

fof(f468,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl2_57 ),
    inference(avatar_component_clause,[],[f466])).

fof(f1769,plain,
    ( spl2_73
    | ~ spl2_25
    | ~ spl2_68 ),
    inference(avatar_split_clause,[],[f1760,f585,f210,f611])).

fof(f1657,plain,
    ( spl2_145
    | ~ spl2_5
    | ~ spl2_24
    | ~ spl2_144 ),
    inference(avatar_split_clause,[],[f1571,f1564,f206,f91,f1654])).

fof(f206,plain,
    ( spl2_24
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f1564,plain,
    ( spl2_144
  <=> ! [X0] :
        ( k1_tops_1(sK0,X0) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_144])])).

fof(f1571,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_5
    | ~ spl2_24
    | ~ spl2_144 ),
    inference(subsumption_resolution,[],[f1568,f93])).

fof(f1568,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_24
    | ~ spl2_144 ),
    inference(resolution,[],[f1565,f208])).

fof(f208,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f206])).

fof(f1565,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = X0 )
    | ~ spl2_144 ),
    inference(avatar_component_clause,[],[f1564])).

fof(f1566,plain,
    ( spl2_144
    | ~ spl2_2
    | ~ spl2_139 ),
    inference(avatar_split_clause,[],[f1562,f1348,f78,f1564])).

fof(f1348,plain,
    ( spl2_139
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_139])])).

fof(f1562,plain,
    ( ! [X0] :
        ( k1_tops_1(sK0,X0) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl2_2
    | ~ spl2_139 ),
    inference(resolution,[],[f1349,f80])).

fof(f1349,plain,
    ( ! [X3,X1] :
        ( ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl2_139 ),
    inference(avatar_component_clause,[],[f1348])).

fof(f1375,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_138 ),
    inference(avatar_contradiction_clause,[],[f1364])).

fof(f1364,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_138 ),
    inference(subsumption_resolution,[],[f93,f1352])).

fof(f1352,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_138 ),
    inference(subsumption_resolution,[],[f1351,f80])).

fof(f1351,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_1
    | ~ spl2_138 ),
    inference(resolution,[],[f1346,f75])).

fof(f1346,plain,
    ( ! [X2,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_138 ),
    inference(avatar_component_clause,[],[f1345])).

fof(f1345,plain,
    ( spl2_138
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_138])])).

fof(f1350,plain,
    ( spl2_138
    | spl2_139 ),
    inference(avatar_split_clause,[],[f56,f1348,f1345])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f1239,plain,
    ( spl2_129
    | ~ spl2_63
    | ~ spl2_100 ),
    inference(avatar_split_clause,[],[f898,f884,f515,f1236])).

fof(f515,plain,
    ( spl2_63
  <=> ! [X2] : k4_xboole_0(sK1,X2) = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(sK1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).

fof(f884,plain,
    ( spl2_100
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_100])])).

fof(f898,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_63
    | ~ spl2_100 ),
    inference(superposition,[],[f516,f886])).

fof(f886,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_100 ),
    inference(avatar_component_clause,[],[f884])).

fof(f516,plain,
    ( ! [X2] : k4_xboole_0(sK1,X2) = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(sK1,X2)))
    | ~ spl2_63 ),
    inference(avatar_component_clause,[],[f515])).

fof(f1127,plain,(
    spl2_117 ),
    inference(avatar_split_clause,[],[f55,f1125])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f887,plain,
    ( spl2_100
    | ~ spl2_32
    | ~ spl2_98 ),
    inference(avatar_split_clause,[],[f865,f861,f255,f884])).

fof(f255,plain,
    ( spl2_32
  <=> ! [X15] : k7_subset_1(u1_struct_0(sK0),sK1,X15) = k4_xboole_0(sK1,X15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f861,plain,
    ( spl2_98
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).

fof(f865,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_32
    | ~ spl2_98 ),
    inference(superposition,[],[f863,f256])).

fof(f256,plain,
    ( ! [X15] : k7_subset_1(u1_struct_0(sK0),sK1,X15) = k4_xboole_0(sK1,X15)
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f255])).

fof(f863,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_98 ),
    inference(avatar_component_clause,[],[f861])).

fof(f864,plain,
    ( spl2_98
    | ~ spl2_5
    | ~ spl2_97 ),
    inference(avatar_split_clause,[],[f859,f843,f91,f861])).

fof(f843,plain,
    ( spl2_97
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_97])])).

fof(f859,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_97 ),
    inference(resolution,[],[f844,f93])).

fof(f844,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_97 ),
    inference(avatar_component_clause,[],[f843])).

fof(f845,plain,
    ( spl2_97
    | ~ spl2_2
    | ~ spl2_75 ),
    inference(avatar_split_clause,[],[f748,f637,f78,f843])).

fof(f637,plain,
    ( spl2_75
  <=> ! [X1,X0] :
        ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).

fof(f748,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_2
    | ~ spl2_75 ),
    inference(resolution,[],[f638,f80])).

fof(f638,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) )
    | ~ spl2_75 ),
    inference(avatar_component_clause,[],[f637])).

fof(f639,plain,(
    spl2_75 ),
    inference(avatar_split_clause,[],[f54,f637])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f587,plain,
    ( spl2_68
    | ~ spl2_26
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f574,f237,f218,f585])).

fof(f218,plain,
    ( spl2_26
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f237,plain,
    ( spl2_30
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f574,plain,
    ( ! [X1] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X1) = k4_xboole_0(k2_pre_topc(sK0,sK1),X1)
    | ~ spl2_26
    | ~ spl2_30 ),
    inference(resolution,[],[f219,f238])).

fof(f238,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f237])).

fof(f219,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f218])).

fof(f571,plain,
    ( ~ spl2_5
    | spl2_26
    | ~ spl2_67 ),
    inference(avatar_contradiction_clause,[],[f570])).

fof(f570,plain,
    ( $false
    | ~ spl2_5
    | spl2_26
    | ~ spl2_67 ),
    inference(subsumption_resolution,[],[f564,f93])).

fof(f564,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_26
    | ~ spl2_67 ),
    inference(resolution,[],[f562,f220])).

fof(f220,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_26 ),
    inference(avatar_component_clause,[],[f218])).

fof(f562,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_67 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl2_67
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).

fof(f563,plain,
    ( spl2_67
    | ~ spl2_2
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f559,f369,f78,f561])).

fof(f369,plain,
    ( spl2_45
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f559,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_2
    | ~ spl2_45 ),
    inference(resolution,[],[f370,f80])).

fof(f370,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f369])).

fof(f517,plain,
    ( spl2_63
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f459,f434,f120,f116,f515])).

fof(f116,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f120,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f434,plain,
    ( spl2_54
  <=> ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f459,plain,
    ( ! [X2] : k4_xboole_0(sK1,X2) = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(sK1,X2)))
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_54 ),
    inference(backward_demodulation,[],[f455,f456])).

fof(f456,plain,
    ( ! [X3] : k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(sK1,X3)) = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(sK1,X3))
    | ~ spl2_10
    | ~ spl2_54 ),
    inference(resolution,[],[f435,f117])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f435,plain,
    ( ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f434])).

fof(f455,plain,
    ( ! [X2] : k4_xboole_0(sK1,X2) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(sK1,X2)))
    | ~ spl2_11
    | ~ spl2_54 ),
    inference(resolution,[],[f435,f121])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f120])).

fof(f469,plain,
    ( spl2_57
    | ~ spl2_18
    | ~ spl2_23
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f449,f439,f197,f160,f466])).

fof(f160,plain,
    ( spl2_18
  <=> ! [X1,X2] :
        ( k4_xboole_0(X1,X2) = k3_subset_1(X1,X2)
        | ~ r1_tarski(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f197,plain,
    ( spl2_23
  <=> ! [X1,X2] :
        ( k3_subset_1(X1,k3_subset_1(X1,X2)) = X2
        | ~ r1_tarski(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f439,plain,
    ( spl2_55
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f449,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl2_18
    | ~ spl2_23
    | ~ spl2_55 ),
    inference(backward_demodulation,[],[f447,f448])).

fof(f448,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_18
    | ~ spl2_55 ),
    inference(resolution,[],[f440,f161])).

fof(f161,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X2,X1)
        | k4_xboole_0(X1,X2) = k3_subset_1(X1,X2) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f160])).

fof(f440,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_55 ),
    inference(avatar_component_clause,[],[f439])).

fof(f447,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl2_23
    | ~ spl2_55 ),
    inference(resolution,[],[f440,f198])).

fof(f198,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X2,X1)
        | k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f197])).

fof(f445,plain,
    ( ~ spl2_5
    | ~ spl2_31
    | spl2_55 ),
    inference(avatar_contradiction_clause,[],[f444])).

fof(f444,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_31
    | spl2_55 ),
    inference(subsumption_resolution,[],[f443,f93])).

fof(f443,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_31
    | spl2_55 ),
    inference(resolution,[],[f441,f243])).

fof(f243,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl2_31
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,k2_pre_topc(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f441,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl2_55 ),
    inference(avatar_component_clause,[],[f439])).

fof(f442,plain,
    ( ~ spl2_55
    | ~ spl2_6
    | spl2_53 ),
    inference(avatar_split_clause,[],[f437,f430,f96,f439])).

fof(f96,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f430,plain,
    ( spl2_53
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f437,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_6
    | spl2_53 ),
    inference(resolution,[],[f432,f97])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f432,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl2_53 ),
    inference(avatar_component_clause,[],[f430])).

fof(f436,plain,
    ( ~ spl2_53
    | spl2_54
    | ~ spl2_12
    | ~ spl2_50 ),
    inference(avatar_split_clause,[],[f419,f416,f124,f434,f430])).

fof(f124,plain,
    ( spl2_12
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f416,plain,
    ( spl2_50
  <=> ! [X20] : k4_xboole_0(sK1,X20) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f419,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl2_12
    | ~ spl2_50 ),
    inference(superposition,[],[f125,f417])).

fof(f417,plain,
    ( ! [X20] : k4_xboole_0(sK1,X20) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X20)
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f416])).

fof(f125,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f418,plain,
    ( spl2_50
    | ~ spl2_5
    | ~ spl2_49 ),
    inference(avatar_split_clause,[],[f414,f401,f91,f416])).

fof(f401,plain,
    ( spl2_49
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k7_subset_1(k2_pre_topc(sK0,X0),X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f414,plain,
    ( ! [X20] : k4_xboole_0(sK1,X20) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X20)
    | ~ spl2_5
    | ~ spl2_49 ),
    inference(resolution,[],[f402,f93])).

fof(f402,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_xboole_0(X0,X1) = k7_subset_1(k2_pre_topc(sK0,X0),X0,X1) )
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f401])).

fof(f403,plain,
    ( spl2_49
    | ~ spl2_31
    | ~ spl2_41 ),
    inference(avatar_split_clause,[],[f329,f326,f242,f401])).

fof(f326,plain,
    ( spl2_41
  <=> ! [X3,X2,X4] :
        ( k7_subset_1(X2,X3,X4) = k4_xboole_0(X3,X4)
        | ~ r1_tarski(X3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f329,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k7_subset_1(k2_pre_topc(sK0,X0),X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_31
    | ~ spl2_41 ),
    inference(resolution,[],[f327,f243])).

fof(f327,plain,
    ( ! [X4,X2,X3] :
        ( ~ r1_tarski(X3,X2)
        | k7_subset_1(X2,X3,X4) = k4_xboole_0(X3,X4) )
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f326])).

fof(f371,plain,(
    spl2_45 ),
    inference(avatar_split_clause,[],[f65,f369])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f328,plain,
    ( spl2_41
    | ~ spl2_6
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f248,f237,f96,f326])).

fof(f248,plain,
    ( ! [X4,X2,X3] :
        ( k7_subset_1(X2,X3,X4) = k4_xboole_0(X3,X4)
        | ~ r1_tarski(X3,X2) )
    | ~ spl2_6
    | ~ spl2_30 ),
    inference(resolution,[],[f238,f97])).

fof(f273,plain,(
    spl2_34 ),
    inference(avatar_split_clause,[],[f64,f271])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f257,plain,
    ( spl2_32
    | ~ spl2_5
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f253,f237,f91,f255])).

fof(f253,plain,
    ( ! [X15] : k7_subset_1(u1_struct_0(sK0),sK1,X15) = k4_xboole_0(sK1,X15)
    | ~ spl2_5
    | ~ spl2_30 ),
    inference(resolution,[],[f238,f93])).

fof(f244,plain,
    ( spl2_31
    | ~ spl2_2
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f240,f233,f78,f242])).

fof(f233,plain,
    ( spl2_29
  <=> ! [X1,X0] :
        ( r1_tarski(X1,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,k2_pre_topc(sK0,X0)) )
    | ~ spl2_2
    | ~ spl2_29 ),
    inference(resolution,[],[f234,f80])).

fof(f234,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(X1,k2_pre_topc(X0,X1)) )
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f233])).

fof(f239,plain,(
    spl2_30 ),
    inference(avatar_split_clause,[],[f69,f237])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f235,plain,(
    spl2_29 ),
    inference(avatar_split_clause,[],[f53,f233])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f213,plain,
    ( spl2_24
    | spl2_25 ),
    inference(avatar_split_clause,[],[f49,f210,f206])).

fof(f49,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f199,plain,
    ( spl2_23
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f164,f120,f96,f197])).

fof(f164,plain,
    ( ! [X2,X1] :
        ( k3_subset_1(X1,k3_subset_1(X1,X2)) = X2
        | ~ r1_tarski(X2,X1) )
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(resolution,[],[f121,f97])).

fof(f162,plain,
    ( spl2_18
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f132,f116,f96,f160])).

fof(f132,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = k3_subset_1(X1,X2)
        | ~ r1_tarski(X2,X1) )
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(resolution,[],[f117,f97])).

fof(f126,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f68,f124])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f122,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f62,f120])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f118,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f61,f116])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f98,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f66,f96])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f94,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f48,f91])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f47,f78])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f46,f73])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:41:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.40  % (12499)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.45  % (12495)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (12502)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (12498)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (12506)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (12494)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (12504)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (12496)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (12492)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (12509)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (12503)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (12501)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (12497)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (12499)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f3240,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f76,f81,f94,f98,f118,f122,f126,f162,f199,f213,f235,f239,f244,f257,f273,f328,f371,f403,f418,f436,f442,f445,f469,f517,f563,f571,f587,f639,f845,f864,f887,f1127,f1239,f1350,f1375,f1566,f1657,f1769,f1797,f2416,f2772,f2903,f3218,f3236])).
% 0.21/0.49  fof(f3236,plain,(
% 0.21/0.49    ~spl2_68 | ~spl2_129 | spl2_145 | ~spl2_147 | ~spl2_193),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f3235])).
% 0.21/0.49  fof(f3235,plain,(
% 0.21/0.49    $false | (~spl2_68 | ~spl2_129 | spl2_145 | ~spl2_147 | ~spl2_193)),
% 0.21/0.49    inference(subsumption_resolution,[],[f3234,f1655])).
% 0.21/0.49  fof(f1655,plain,(
% 0.21/0.49    sK1 != k1_tops_1(sK0,sK1) | spl2_145),
% 0.21/0.49    inference(avatar_component_clause,[],[f1654])).
% 0.21/0.49  fof(f1654,plain,(
% 0.21/0.49    spl2_145 <=> sK1 = k1_tops_1(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_145])])).
% 0.21/0.49  fof(f3234,plain,(
% 0.21/0.49    sK1 = k1_tops_1(sK0,sK1) | (~spl2_68 | ~spl2_129 | ~spl2_147 | ~spl2_193)),
% 0.21/0.49    inference(forward_demodulation,[],[f3232,f1796])).
% 0.21/0.49  fof(f1796,plain,(
% 0.21/0.49    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_147),
% 0.21/0.49    inference(avatar_component_clause,[],[f1794])).
% 0.21/0.49  fof(f1794,plain,(
% 0.21/0.49    spl2_147 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_147])])).
% 0.21/0.49  fof(f3232,plain,(
% 0.21/0.49    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_68 | ~spl2_129 | ~spl2_193)),
% 0.21/0.49    inference(backward_demodulation,[],[f1238,f3228])).
% 0.21/0.49  fof(f3228,plain,(
% 0.21/0.49    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_68 | ~spl2_193)),
% 0.21/0.49    inference(superposition,[],[f3217,f586])).
% 0.21/0.49  fof(f586,plain,(
% 0.21/0.49    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X1) = k4_xboole_0(k2_pre_topc(sK0,sK1),X1)) ) | ~spl2_68),
% 0.21/0.49    inference(avatar_component_clause,[],[f585])).
% 0.21/0.49  fof(f585,plain,(
% 0.21/0.49    spl2_68 <=> ! [X1] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X1) = k4_xboole_0(k2_pre_topc(sK0,sK1),X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).
% 0.21/0.49  fof(f3217,plain,(
% 0.21/0.49    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_193),
% 0.21/0.49    inference(avatar_component_clause,[],[f3215])).
% 0.21/0.49  fof(f3215,plain,(
% 0.21/0.49    spl2_193 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_193])])).
% 0.21/0.49  fof(f1238,plain,(
% 0.21/0.49    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) | ~spl2_129),
% 0.21/0.49    inference(avatar_component_clause,[],[f1236])).
% 0.21/0.49  fof(f1236,plain,(
% 0.21/0.49    spl2_129 <=> k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_129])])).
% 0.21/0.49  fof(f3218,plain,(
% 0.21/0.49    spl2_193 | ~spl2_5 | ~spl2_178),
% 0.21/0.49    inference(avatar_split_clause,[],[f2900,f2770,f91,f3215])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    spl2_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.49  fof(f2770,plain,(
% 0.21/0.49    spl2_178 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_178])])).
% 0.21/0.49  fof(f2900,plain,(
% 0.21/0.49    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_5 | ~spl2_178)),
% 0.21/0.49    inference(resolution,[],[f2771,f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f91])).
% 0.21/0.49  fof(f2771,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) ) | ~spl2_178),
% 0.21/0.49    inference(avatar_component_clause,[],[f2770])).
% 0.21/0.49  fof(f2903,plain,(
% 0.21/0.49    ~spl2_5 | spl2_25 | ~spl2_145 | ~spl2_178),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f2902])).
% 0.21/0.49  fof(f2902,plain,(
% 0.21/0.49    $false | (~spl2_5 | spl2_25 | ~spl2_145 | ~spl2_178)),
% 0.21/0.49    inference(subsumption_resolution,[],[f2901,f211])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl2_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f210])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    spl2_25 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.49  fof(f2901,plain,(
% 0.21/0.49    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | (~spl2_5 | ~spl2_145 | ~spl2_178)),
% 0.21/0.49    inference(forward_demodulation,[],[f2900,f1656])).
% 0.21/0.49  fof(f1656,plain,(
% 0.21/0.49    sK1 = k1_tops_1(sK0,sK1) | ~spl2_145),
% 0.21/0.49    inference(avatar_component_clause,[],[f1654])).
% 0.21/0.49  fof(f2772,plain,(
% 0.21/0.49    spl2_178 | ~spl2_2 | ~spl2_117),
% 0.21/0.49    inference(avatar_split_clause,[],[f1221,f1125,f78,f2770])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl2_2 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.49  fof(f1125,plain,(
% 0.21/0.49    spl2_117 <=> ! [X1,X0] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_117])])).
% 0.21/0.49  fof(f1221,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) ) | (~spl2_2 | ~spl2_117)),
% 0.21/0.49    inference(resolution,[],[f1126,f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f78])).
% 0.21/0.49  fof(f1126,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) ) | ~spl2_117),
% 0.21/0.49    inference(avatar_component_clause,[],[f1125])).
% 0.21/0.49  fof(f2416,plain,(
% 0.21/0.49    ~spl2_73 | ~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_34 | ~spl2_68 | ~spl2_145),
% 0.21/0.49    inference(avatar_split_clause,[],[f2380,f1654,f585,f271,f91,f78,f73,f611])).
% 0.21/0.49  fof(f611,plain,(
% 0.21/0.49    spl2_73 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl2_1 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.49  fof(f271,plain,(
% 0.21/0.49    spl2_34 <=> ! [X1,X0] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.49  fof(f2380,plain,(
% 0.21/0.49    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_34 | ~spl2_68 | ~spl2_145)),
% 0.21/0.49    inference(subsumption_resolution,[],[f602,f2379])).
% 0.21/0.49  fof(f2379,plain,(
% 0.21/0.49    v3_pre_topc(sK1,sK0) | (~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_34 | ~spl2_145)),
% 0.21/0.49    inference(subsumption_resolution,[],[f2378,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    v2_pre_topc(sK0) | ~spl2_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f73])).
% 0.21/0.49  fof(f2378,plain,(
% 0.21/0.49    v3_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | (~spl2_2 | ~spl2_5 | ~spl2_34 | ~spl2_145)),
% 0.21/0.49    inference(subsumption_resolution,[],[f2377,f80])).
% 0.21/0.49  fof(f2377,plain,(
% 0.21/0.49    v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl2_5 | ~spl2_34 | ~spl2_145)),
% 0.21/0.49    inference(subsumption_resolution,[],[f2371,f93])).
% 0.21/0.49  fof(f2371,plain,(
% 0.21/0.49    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl2_34 | ~spl2_145)),
% 0.21/0.49    inference(superposition,[],[f272,f1656])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl2_34),
% 0.21/0.49    inference(avatar_component_clause,[],[f271])).
% 0.21/0.49  fof(f602,plain,(
% 0.21/0.49    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0) | ~spl2_68),
% 0.21/0.49    inference(forward_demodulation,[],[f50,f586])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f19])).
% 0.21/0.49  fof(f19,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 0.21/0.49  % (12500)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  fof(f1797,plain,(
% 0.21/0.49    spl2_147 | ~spl2_25 | ~spl2_57 | ~spl2_68),
% 0.21/0.49    inference(avatar_split_clause,[],[f1767,f585,f466,f210,f1794])).
% 0.21/0.49  fof(f466,plain,(
% 0.21/0.49    spl2_57 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 0.21/0.49  fof(f1767,plain,(
% 0.21/0.49    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_25 | ~spl2_57 | ~spl2_68)),
% 0.21/0.49    inference(backward_demodulation,[],[f468,f1760])).
% 0.21/0.49  fof(f1760,plain,(
% 0.21/0.49    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl2_25 | ~spl2_68)),
% 0.21/0.49    inference(superposition,[],[f586,f212])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f210])).
% 0.21/0.49  fof(f468,plain,(
% 0.21/0.49    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) | ~spl2_57),
% 0.21/0.49    inference(avatar_component_clause,[],[f466])).
% 0.21/0.49  fof(f1769,plain,(
% 0.21/0.49    spl2_73 | ~spl2_25 | ~spl2_68),
% 0.21/0.49    inference(avatar_split_clause,[],[f1760,f585,f210,f611])).
% 0.21/0.49  fof(f1657,plain,(
% 0.21/0.49    spl2_145 | ~spl2_5 | ~spl2_24 | ~spl2_144),
% 0.21/0.49    inference(avatar_split_clause,[],[f1571,f1564,f206,f91,f1654])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    spl2_24 <=> v3_pre_topc(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.49  fof(f1564,plain,(
% 0.21/0.49    spl2_144 <=> ! [X0] : (k1_tops_1(sK0,X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_144])])).
% 0.21/0.49  fof(f1571,plain,(
% 0.21/0.49    sK1 = k1_tops_1(sK0,sK1) | (~spl2_5 | ~spl2_24 | ~spl2_144)),
% 0.21/0.49    inference(subsumption_resolution,[],[f1568,f93])).
% 0.21/0.49  fof(f1568,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k1_tops_1(sK0,sK1) | (~spl2_24 | ~spl2_144)),
% 0.21/0.49    inference(resolution,[],[f1565,f208])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    v3_pre_topc(sK1,sK0) | ~spl2_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f206])).
% 0.21/0.49  fof(f1565,plain,(
% 0.21/0.49    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = X0) ) | ~spl2_144),
% 0.21/0.49    inference(avatar_component_clause,[],[f1564])).
% 0.21/0.49  fof(f1566,plain,(
% 0.21/0.49    spl2_144 | ~spl2_2 | ~spl2_139),
% 0.21/0.49    inference(avatar_split_clause,[],[f1562,f1348,f78,f1564])).
% 0.21/0.49  fof(f1348,plain,(
% 0.21/0.49    spl2_139 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_139])])).
% 0.21/0.49  fof(f1562,plain,(
% 0.21/0.49    ( ! [X0] : (k1_tops_1(sK0,X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0)) ) | (~spl2_2 | ~spl2_139)),
% 0.21/0.49    inference(resolution,[],[f1349,f80])).
% 0.21/0.49  fof(f1349,plain,(
% 0.21/0.49    ( ! [X3,X1] : (~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1)) ) | ~spl2_139),
% 0.21/0.49    inference(avatar_component_clause,[],[f1348])).
% 0.21/0.49  fof(f1375,plain,(
% 0.21/0.49    ~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_138),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f1364])).
% 0.21/0.49  fof(f1364,plain,(
% 0.21/0.49    $false | (~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_138)),
% 0.21/0.49    inference(subsumption_resolution,[],[f93,f1352])).
% 0.21/0.49  fof(f1352,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_1 | ~spl2_2 | ~spl2_138)),
% 0.21/0.49    inference(subsumption_resolution,[],[f1351,f80])).
% 0.21/0.49  fof(f1351,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | (~spl2_1 | ~spl2_138)),
% 0.21/0.49    inference(resolution,[],[f1346,f75])).
% 0.21/0.49  fof(f1346,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_138),
% 0.21/0.49    inference(avatar_component_clause,[],[f1345])).
% 0.21/0.49  fof(f1345,plain,(
% 0.21/0.49    spl2_138 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_138])])).
% 0.21/0.49  fof(f1350,plain,(
% 0.21/0.49    spl2_138 | spl2_139),
% 0.21/0.49    inference(avatar_split_clause,[],[f56,f1348,f1345])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 0.21/0.49  fof(f1239,plain,(
% 0.21/0.49    spl2_129 | ~spl2_63 | ~spl2_100),
% 0.21/0.49    inference(avatar_split_clause,[],[f898,f884,f515,f1236])).
% 0.21/0.49  fof(f515,plain,(
% 0.21/0.49    spl2_63 <=> ! [X2] : k4_xboole_0(sK1,X2) = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(sK1,X2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).
% 0.21/0.49  fof(f884,plain,(
% 0.21/0.49    spl2_100 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_100])])).
% 0.21/0.49  fof(f898,plain,(
% 0.21/0.49    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) | (~spl2_63 | ~spl2_100)),
% 0.21/0.49    inference(superposition,[],[f516,f886])).
% 0.21/0.49  fof(f886,plain,(
% 0.21/0.49    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_100),
% 0.21/0.49    inference(avatar_component_clause,[],[f884])).
% 0.21/0.49  fof(f516,plain,(
% 0.21/0.49    ( ! [X2] : (k4_xboole_0(sK1,X2) = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(sK1,X2)))) ) | ~spl2_63),
% 0.21/0.49    inference(avatar_component_clause,[],[f515])).
% 0.21/0.49  fof(f1127,plain,(
% 0.21/0.49    spl2_117),
% 0.21/0.49    inference(avatar_split_clause,[],[f55,f1125])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.21/0.49  fof(f887,plain,(
% 0.21/0.49    spl2_100 | ~spl2_32 | ~spl2_98),
% 0.21/0.49    inference(avatar_split_clause,[],[f865,f861,f255,f884])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    spl2_32 <=> ! [X15] : k7_subset_1(u1_struct_0(sK0),sK1,X15) = k4_xboole_0(sK1,X15)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.21/0.49  fof(f861,plain,(
% 0.21/0.49    spl2_98 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).
% 0.21/0.49  fof(f865,plain,(
% 0.21/0.49    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_32 | ~spl2_98)),
% 0.21/0.49    inference(superposition,[],[f863,f256])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    ( ! [X15] : (k7_subset_1(u1_struct_0(sK0),sK1,X15) = k4_xboole_0(sK1,X15)) ) | ~spl2_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f255])).
% 0.21/0.49  fof(f863,plain,(
% 0.21/0.49    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_98),
% 0.21/0.49    inference(avatar_component_clause,[],[f861])).
% 0.21/0.49  fof(f864,plain,(
% 0.21/0.49    spl2_98 | ~spl2_5 | ~spl2_97),
% 0.21/0.49    inference(avatar_split_clause,[],[f859,f843,f91,f861])).
% 0.21/0.49  fof(f843,plain,(
% 0.21/0.49    spl2_97 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_97])])).
% 0.21/0.49  fof(f859,plain,(
% 0.21/0.49    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_5 | ~spl2_97)),
% 0.21/0.49    inference(resolution,[],[f844,f93])).
% 0.21/0.49  fof(f844,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | ~spl2_97),
% 0.21/0.49    inference(avatar_component_clause,[],[f843])).
% 0.21/0.49  fof(f845,plain,(
% 0.21/0.49    spl2_97 | ~spl2_2 | ~spl2_75),
% 0.21/0.49    inference(avatar_split_clause,[],[f748,f637,f78,f843])).
% 0.21/0.49  fof(f637,plain,(
% 0.21/0.49    spl2_75 <=> ! [X1,X0] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).
% 0.21/0.49  fof(f748,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | (~spl2_2 | ~spl2_75)),
% 0.21/0.49    inference(resolution,[],[f638,f80])).
% 0.21/0.49  fof(f638,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) ) | ~spl2_75),
% 0.21/0.49    inference(avatar_component_clause,[],[f637])).
% 0.21/0.49  fof(f639,plain,(
% 0.21/0.49    spl2_75),
% 0.21/0.49    inference(avatar_split_clause,[],[f54,f637])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 0.21/0.49  fof(f587,plain,(
% 0.21/0.49    spl2_68 | ~spl2_26 | ~spl2_30),
% 0.21/0.49    inference(avatar_split_clause,[],[f574,f237,f218,f585])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    spl2_26 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    spl2_30 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.21/0.49  fof(f574,plain,(
% 0.21/0.49    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X1) = k4_xboole_0(k2_pre_topc(sK0,sK1),X1)) ) | (~spl2_26 | ~spl2_30)),
% 0.21/0.49    inference(resolution,[],[f219,f238])).
% 0.21/0.49  fof(f238,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) ) | ~spl2_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f237])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f218])).
% 0.21/0.49  fof(f571,plain,(
% 0.21/0.49    ~spl2_5 | spl2_26 | ~spl2_67),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f570])).
% 0.21/0.49  fof(f570,plain,(
% 0.21/0.49    $false | (~spl2_5 | spl2_26 | ~spl2_67)),
% 0.21/0.49    inference(subsumption_resolution,[],[f564,f93])).
% 0.21/0.49  fof(f564,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl2_26 | ~spl2_67)),
% 0.21/0.49    inference(resolution,[],[f562,f220])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f218])).
% 0.21/0.49  fof(f562,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_67),
% 0.21/0.49    inference(avatar_component_clause,[],[f561])).
% 0.21/0.49  fof(f561,plain,(
% 0.21/0.49    spl2_67 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).
% 0.21/0.49  fof(f563,plain,(
% 0.21/0.49    spl2_67 | ~spl2_2 | ~spl2_45),
% 0.21/0.49    inference(avatar_split_clause,[],[f559,f369,f78,f561])).
% 0.21/0.49  fof(f369,plain,(
% 0.21/0.49    spl2_45 <=> ! [X1,X0] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.21/0.49  fof(f559,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_2 | ~spl2_45)),
% 0.21/0.49    inference(resolution,[],[f370,f80])).
% 0.21/0.49  fof(f370,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl2_45),
% 0.21/0.49    inference(avatar_component_clause,[],[f369])).
% 0.21/0.49  fof(f517,plain,(
% 0.21/0.49    spl2_63 | ~spl2_10 | ~spl2_11 | ~spl2_54),
% 0.21/0.49    inference(avatar_split_clause,[],[f459,f434,f120,f116,f515])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl2_10 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl2_11 <=> ! [X1,X0] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.49  fof(f434,plain,(
% 0.21/0.49    spl2_54 <=> ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 0.21/0.49  fof(f459,plain,(
% 0.21/0.49    ( ! [X2] : (k4_xboole_0(sK1,X2) = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(sK1,X2)))) ) | (~spl2_10 | ~spl2_11 | ~spl2_54)),
% 0.21/0.49    inference(backward_demodulation,[],[f455,f456])).
% 0.21/0.49  fof(f456,plain,(
% 0.21/0.49    ( ! [X3] : (k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(sK1,X3)) = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(sK1,X3))) ) | (~spl2_10 | ~spl2_54)),
% 0.21/0.49    inference(resolution,[],[f435,f117])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) ) | ~spl2_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f116])).
% 0.21/0.49  fof(f435,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl2_54),
% 0.21/0.49    inference(avatar_component_clause,[],[f434])).
% 0.21/0.49  fof(f455,plain,(
% 0.21/0.49    ( ! [X2] : (k4_xboole_0(sK1,X2) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(sK1,X2)))) ) | (~spl2_11 | ~spl2_54)),
% 0.21/0.49    inference(resolution,[],[f435,f121])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) ) | ~spl2_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f120])).
% 0.21/0.49  fof(f469,plain,(
% 0.21/0.49    spl2_57 | ~spl2_18 | ~spl2_23 | ~spl2_55),
% 0.21/0.49    inference(avatar_split_clause,[],[f449,f439,f197,f160,f466])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    spl2_18 <=> ! [X1,X2] : (k4_xboole_0(X1,X2) = k3_subset_1(X1,X2) | ~r1_tarski(X2,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    spl2_23 <=> ! [X1,X2] : (k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 | ~r1_tarski(X2,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.49  fof(f439,plain,(
% 0.21/0.49    spl2_55 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 0.21/0.49  fof(f449,plain,(
% 0.21/0.49    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) | (~spl2_18 | ~spl2_23 | ~spl2_55)),
% 0.21/0.49    inference(backward_demodulation,[],[f447,f448])).
% 0.21/0.49  fof(f448,plain,(
% 0.21/0.49    k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl2_18 | ~spl2_55)),
% 0.21/0.49    inference(resolution,[],[f440,f161])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k4_xboole_0(X1,X2) = k3_subset_1(X1,X2)) ) | ~spl2_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f160])).
% 0.21/0.49  fof(f440,plain,(
% 0.21/0.49    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_55),
% 0.21/0.49    inference(avatar_component_clause,[],[f439])).
% 0.21/0.49  fof(f447,plain,(
% 0.21/0.49    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) | (~spl2_23 | ~spl2_55)),
% 0.21/0.49    inference(resolution,[],[f440,f198])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k3_subset_1(X1,k3_subset_1(X1,X2)) = X2) ) | ~spl2_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f197])).
% 0.21/0.49  fof(f445,plain,(
% 0.21/0.49    ~spl2_5 | ~spl2_31 | spl2_55),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f444])).
% 0.21/0.49  fof(f444,plain,(
% 0.21/0.49    $false | (~spl2_5 | ~spl2_31 | spl2_55)),
% 0.21/0.49    inference(subsumption_resolution,[],[f443,f93])).
% 0.21/0.49  fof(f443,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_31 | spl2_55)),
% 0.21/0.49    inference(resolution,[],[f441,f243])).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(X0,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_31),
% 0.21/0.49    inference(avatar_component_clause,[],[f242])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    spl2_31 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k2_pre_topc(sK0,X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.21/0.49  fof(f441,plain,(
% 0.21/0.49    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl2_55),
% 0.21/0.49    inference(avatar_component_clause,[],[f439])).
% 0.21/0.49  fof(f442,plain,(
% 0.21/0.49    ~spl2_55 | ~spl2_6 | spl2_53),
% 0.21/0.49    inference(avatar_split_clause,[],[f437,f430,f96,f439])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl2_6 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.49  fof(f430,plain,(
% 0.21/0.49    spl2_53 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 0.21/0.49  fof(f437,plain,(
% 0.21/0.49    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_6 | spl2_53)),
% 0.21/0.49    inference(resolution,[],[f432,f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f96])).
% 0.21/0.49  fof(f432,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl2_53),
% 0.21/0.49    inference(avatar_component_clause,[],[f430])).
% 0.21/0.49  fof(f436,plain,(
% 0.21/0.49    ~spl2_53 | spl2_54 | ~spl2_12 | ~spl2_50),
% 0.21/0.49    inference(avatar_split_clause,[],[f419,f416,f124,f434,f430])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    spl2_12 <=> ! [X1,X0,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.49  fof(f416,plain,(
% 0.21/0.49    spl2_50 <=> ! [X20] : k4_xboole_0(sK1,X20) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X20)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 0.21/0.49  fof(f419,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | (~spl2_12 | ~spl2_50)),
% 0.21/0.49    inference(superposition,[],[f125,f417])).
% 0.21/0.49  fof(f417,plain,(
% 0.21/0.49    ( ! [X20] : (k4_xboole_0(sK1,X20) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X20)) ) | ~spl2_50),
% 0.21/0.49    inference(avatar_component_clause,[],[f416])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f124])).
% 0.21/0.49  fof(f418,plain,(
% 0.21/0.49    spl2_50 | ~spl2_5 | ~spl2_49),
% 0.21/0.49    inference(avatar_split_clause,[],[f414,f401,f91,f416])).
% 0.21/0.49  fof(f401,plain,(
% 0.21/0.49    spl2_49 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k7_subset_1(k2_pre_topc(sK0,X0),X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 0.21/0.49  fof(f414,plain,(
% 0.21/0.49    ( ! [X20] : (k4_xboole_0(sK1,X20) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X20)) ) | (~spl2_5 | ~spl2_49)),
% 0.21/0.49    inference(resolution,[],[f402,f93])).
% 0.21/0.50  fof(f402,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_xboole_0(X0,X1) = k7_subset_1(k2_pre_topc(sK0,X0),X0,X1)) ) | ~spl2_49),
% 0.21/0.50    inference(avatar_component_clause,[],[f401])).
% 0.21/0.50  fof(f403,plain,(
% 0.21/0.50    spl2_49 | ~spl2_31 | ~spl2_41),
% 0.21/0.50    inference(avatar_split_clause,[],[f329,f326,f242,f401])).
% 0.21/0.50  fof(f326,plain,(
% 0.21/0.50    spl2_41 <=> ! [X3,X2,X4] : (k7_subset_1(X2,X3,X4) = k4_xboole_0(X3,X4) | ~r1_tarski(X3,X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 0.21/0.50  fof(f329,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k7_subset_1(k2_pre_topc(sK0,X0),X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_31 | ~spl2_41)),
% 0.21/0.50    inference(resolution,[],[f327,f243])).
% 0.21/0.50  fof(f327,plain,(
% 0.21/0.50    ( ! [X4,X2,X3] : (~r1_tarski(X3,X2) | k7_subset_1(X2,X3,X4) = k4_xboole_0(X3,X4)) ) | ~spl2_41),
% 0.21/0.50    inference(avatar_component_clause,[],[f326])).
% 0.21/0.50  fof(f371,plain,(
% 0.21/0.50    spl2_45),
% 0.21/0.50    inference(avatar_split_clause,[],[f65,f369])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.50  fof(f328,plain,(
% 0.21/0.50    spl2_41 | ~spl2_6 | ~spl2_30),
% 0.21/0.50    inference(avatar_split_clause,[],[f248,f237,f96,f326])).
% 0.21/0.50  fof(f248,plain,(
% 0.21/0.50    ( ! [X4,X2,X3] : (k7_subset_1(X2,X3,X4) = k4_xboole_0(X3,X4) | ~r1_tarski(X3,X2)) ) | (~spl2_6 | ~spl2_30)),
% 0.21/0.50    inference(resolution,[],[f238,f97])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    spl2_34),
% 0.21/0.50    inference(avatar_split_clause,[],[f64,f271])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    spl2_32 | ~spl2_5 | ~spl2_30),
% 0.21/0.50    inference(avatar_split_clause,[],[f253,f237,f91,f255])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    ( ! [X15] : (k7_subset_1(u1_struct_0(sK0),sK1,X15) = k4_xboole_0(sK1,X15)) ) | (~spl2_5 | ~spl2_30)),
% 0.21/0.50    inference(resolution,[],[f238,f93])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    spl2_31 | ~spl2_2 | ~spl2_29),
% 0.21/0.50    inference(avatar_split_clause,[],[f240,f233,f78,f242])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    spl2_29 <=> ! [X1,X0] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k2_pre_topc(sK0,X0))) ) | (~spl2_2 | ~spl2_29)),
% 0.21/0.50    inference(resolution,[],[f234,f80])).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) ) | ~spl2_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f233])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    spl2_30),
% 0.21/0.50    inference(avatar_split_clause,[],[f69,f237])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    spl2_29),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f233])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    spl2_24 | spl2_25),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f210,f206])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    spl2_23 | ~spl2_6 | ~spl2_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f164,f120,f96,f197])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 | ~r1_tarski(X2,X1)) ) | (~spl2_6 | ~spl2_11)),
% 0.21/0.50    inference(resolution,[],[f121,f97])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    spl2_18 | ~spl2_6 | ~spl2_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f132,f116,f96,f160])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k3_subset_1(X1,X2) | ~r1_tarski(X2,X1)) ) | (~spl2_6 | ~spl2_10)),
% 0.21/0.50    inference(resolution,[],[f117,f97])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl2_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f68,f124])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl2_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f62,f120])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    spl2_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f61,f116])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl2_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f66,f96])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.50    inference(unused_predicate_definition_removal,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    spl2_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f91])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    spl2_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f78])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl2_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f46,f73])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (12499)------------------------------
% 0.21/0.50  % (12499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12499)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (12499)Memory used [KB]: 8315
% 0.21/0.50  % (12499)Time elapsed: 0.094 s
% 0.21/0.50  % (12499)------------------------------
% 0.21/0.50  % (12499)------------------------------
% 0.21/0.50  % (12491)Success in time 0.147 s
%------------------------------------------------------------------------------

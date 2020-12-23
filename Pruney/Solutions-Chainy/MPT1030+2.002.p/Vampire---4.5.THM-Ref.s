%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 (  95 expanded)
%              Number of leaves         :   18 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :  174 ( 306 expanded)
%              Number of equality atoms :   28 (  61 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f33,f40,f44,f48,f61,f65,f69,f70,f75,f76])).

fof(f76,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != sK0
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f75,plain,
    ( spl3_4
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | spl3_4
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f72,f39])).

fof(f39,plain,
    ( k1_xboole_0 != sK1
    | spl3_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f72,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_9 ),
    inference(resolution,[],[f71,f25])).

fof(f25,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f71,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK1 = X0 )
    | ~ spl3_9 ),
    inference(resolution,[],[f64,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f64,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_9
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f70,plain,
    ( sK2 != k3_partfun1(sK2,sK0,sK1)
    | v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0)
    | ~ v1_partfun1(sK2,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f69,plain,
    ( spl3_10
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f52,f42,f27,f67])).

fof(f67,plain,
    ( spl3_10
  <=> sK2 = k3_partfun1(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f27,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f42,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f52,plain,
    ( sK2 = k3_partfun1(sK2,sK0,sK1)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f49,f28])).

fof(f28,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f49,plain,
    ( ~ v1_funct_1(sK2)
    | sK2 = k3_partfun1(sK2,sK0,sK1)
    | ~ spl3_5 ),
    inference(resolution,[],[f43,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k3_partfun1(X2,X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k3_partfun1(X2,X0,X1) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_partfun1)).

fof(f43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f65,plain,
    ( spl3_7
    | spl3_9
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f54,f42,f31,f27,f63,f56])).

fof(f56,plain,
    ( spl3_7
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f31,plain,
    ( spl3_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f54,plain,
    ( v1_xboole_0(sK1)
    | v1_partfun1(sK2,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f53,f32])).

fof(f32,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f53,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v1_partfun1(sK2,sK0)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f50,f28])).

fof(f50,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v1_partfun1(sK2,sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f43,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f61,plain,
    ( spl3_7
    | ~ spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f51,f42,f59,f56])).

fof(f59,plain,
    ( spl3_8
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f51,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_partfun1(sK2,sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f43,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f48,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f46,plain,
    ( spl3_6
  <=> v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f20,plain,(
    ~ v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(k3_partfun1(X2,X0,X1),X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(k3_partfun1(X2,X0,X1),X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => v1_partfun1(k3_partfun1(X2,X0,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => v1_partfun1(k3_partfun1(X2,X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_funct_2)).

fof(f44,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f42])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,
    ( spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f16,f38,f35])).

fof(f35,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f16,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f31])).

fof(f18,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f29,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f17,f27])).

fof(f17,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (24219)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (24219)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (24226)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f29,f33,f40,f44,f48,f61,f65,f69,f70,f75,f76])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    k1_xboole_0 != sK1 | k1_xboole_0 != sK0 | ~v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 0.22/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    spl3_4 | ~spl3_9),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f74])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    $false | (spl3_4 | ~spl3_9)),
% 0.22/0.48    inference(subsumption_resolution,[],[f72,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    k1_xboole_0 != sK1 | spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    spl3_4 <=> k1_xboole_0 = sK1),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    k1_xboole_0 = sK1 | ~spl3_9),
% 0.22/0.48    inference(resolution,[],[f71,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(X0) | sK1 = X0) ) | ~spl3_9),
% 0.22/0.48    inference(resolution,[],[f64,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    v1_xboole_0(sK1) | ~spl3_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    spl3_9 <=> v1_xboole_0(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    sK2 != k3_partfun1(sK2,sK0,sK1) | v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0) | ~v1_partfun1(sK2,sK0)),
% 0.22/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    spl3_10 | ~spl3_1 | ~spl3_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f52,f42,f27,f67])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    spl3_10 <=> sK2 = k3_partfun1(sK2,sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    spl3_1 <=> v1_funct_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    sK2 = k3_partfun1(sK2,sK0,sK1) | (~spl3_1 | ~spl3_5)),
% 0.22/0.48    inference(subsumption_resolution,[],[f49,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    v1_funct_1(sK2) | ~spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f27])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ~v1_funct_1(sK2) | sK2 = k3_partfun1(sK2,sK0,sK1) | ~spl3_5),
% 0.22/0.48    inference(resolution,[],[f43,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k3_partfun1(X2,X0,X1) = X2) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.48    inference(flattening,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k3_partfun1(X2,X0,X1) = X2)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_partfun1)).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f42])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    spl3_7 | spl3_9 | ~spl3_1 | ~spl3_2 | ~spl3_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f54,f42,f31,f27,f63,f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    spl3_7 <=> v1_partfun1(sK2,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    spl3_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    v1_xboole_0(sK1) | v1_partfun1(sK2,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_5)),
% 0.22/0.48    inference(subsumption_resolution,[],[f53,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    v1_funct_2(sK2,sK0,sK1) | ~spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f31])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    v1_xboole_0(sK1) | ~v1_funct_2(sK2,sK0,sK1) | v1_partfun1(sK2,sK0) | (~spl3_1 | ~spl3_5)),
% 0.22/0.48    inference(subsumption_resolution,[],[f50,f28])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    v1_xboole_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | v1_partfun1(sK2,sK0) | ~spl3_5),
% 0.22/0.48    inference(resolution,[],[f43,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.48    inference(flattening,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    spl3_7 | ~spl3_8 | ~spl3_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f51,f42,f59,f56])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    spl3_8 <=> v1_xboole_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ~v1_xboole_0(sK0) | v1_partfun1(sK2,sK0) | ~spl3_5),
% 0.22/0.48    inference(resolution,[],[f43,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_partfun1(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ~spl3_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f20,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    spl3_6 <=> v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ~v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (~v1_partfun1(k3_partfun1(X2,X0,X1),X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.48    inference(flattening,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0,X1,X2] : ((~v1_partfun1(k3_partfun1(X2,X0,X1),X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => v1_partfun1(k3_partfun1(X2,X0,X1),X0)))),
% 0.22/0.48    inference(negated_conjecture,[],[f6])).
% 0.22/0.48  fof(f6,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => v1_partfun1(k3_partfun1(X2,X0,X1),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_funct_2)).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    spl3_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f42])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    spl3_3 | ~spl3_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f16,f38,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    spl3_3 <=> k1_xboole_0 = sK0),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    spl3_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f18,f31])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    spl3_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f17,f27])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    v1_funct_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (24219)------------------------------
% 0.22/0.48  % (24219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (24219)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (24219)Memory used [KB]: 6140
% 0.22/0.48  % (24219)Time elapsed: 0.062 s
% 0.22/0.48  % (24219)------------------------------
% 0.22/0.48  % (24219)------------------------------
% 0.22/0.49  % (24218)Success in time 0.126 s
%------------------------------------------------------------------------------

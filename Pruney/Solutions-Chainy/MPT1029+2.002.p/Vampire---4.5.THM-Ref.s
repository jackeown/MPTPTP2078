%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 115 expanded)
%              Number of leaves         :   16 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :  205 ( 483 expanded)
%              Number of equality atoms :   25 (  89 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f37,f45,f50,f51,f55,f66,f71,f79,f88,f91])).

fof(f91,plain,
    ( ~ spl3_7
    | ~ spl3_9
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_9
    | spl3_11 ),
    inference(subsumption_resolution,[],[f78,f89])).

fof(f89,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ spl3_7
    | spl3_11 ),
    inference(resolution,[],[f87,f58])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( v1_partfun1(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
    | ~ spl3_7 ),
    inference(resolution,[],[f25,f54])).

fof(f54,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f87,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_11
  <=> v1_partfun1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f78,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f88,plain,
    ( ~ spl3_11
    | spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f74,f35,f28,f86])).

fof(f28,plain,
    ( spl3_1
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f35,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f74,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f29,f36])).

fof(f36,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f29,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f79,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f75,f39,f35,f32,f77])).

fof(f32,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f39,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f75,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f72,f70])).

fof(f70,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f72,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(superposition,[],[f40,f36])).

fof(f40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f71,plain,
    ( spl3_2
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f68,f62,f53,f32])).

fof(f62,plain,
    ( spl3_8
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f68,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(resolution,[],[f63,f56])).

fof(f56,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_7 ),
    inference(resolution,[],[f26,f54])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f63,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f66,plain,
    ( spl3_8
    | ~ spl3_5
    | spl3_1
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f60,f47,f39,f28,f43,f62])).

fof(f43,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f47,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f60,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v1_xboole_0(sK1)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(resolution,[],[f59,f40])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_partfun1(sK2,X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_xboole_0(X1) )
    | ~ spl3_6 ),
    inference(resolution,[],[f24,f48])).

fof(f48,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f55,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f51,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f15,f47])).

fof(f15,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ v1_partfun1(sK2,sK0)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ v1_partfun1(X2,X0)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ~ v1_partfun1(sK2,sK0)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) )
         => ( v1_partfun1(X2,X0)
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f50,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f16,f39])).

fof(f16,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f43])).

fof(f18,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f20,f35,f32])).

fof(f20,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f28])).

fof(f21,plain,(
    ~ v1_partfun1(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:41:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (31485)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (31485)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f30,f37,f45,f50,f51,f55,f66,f71,f79,f88,f91])).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    ~spl3_7 | ~spl3_9 | spl3_11),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f90])).
% 0.22/0.47  fof(f90,plain,(
% 0.22/0.47    $false | (~spl3_7 | ~spl3_9 | spl3_11)),
% 0.22/0.47    inference(subsumption_resolution,[],[f78,f89])).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl3_7 | spl3_11)),
% 0.22/0.47    inference(resolution,[],[f87,f58])).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_partfun1(X0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) ) | ~spl3_7),
% 0.22/0.47    inference(resolution,[],[f25,f54])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0) | ~spl3_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f53])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    spl3_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.22/0.47  fof(f87,plain,(
% 0.22/0.47    ~v1_partfun1(sK2,k1_xboole_0) | spl3_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f86])).
% 0.22/0.47  fof(f86,plain,(
% 0.22/0.47    spl3_11 <=> v1_partfun1(sK2,k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f77])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    spl3_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    ~spl3_11 | spl3_1 | ~spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f74,f35,f28,f86])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    spl3_1 <=> v1_partfun1(sK2,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    spl3_3 <=> k1_xboole_0 = sK0),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    ~v1_partfun1(sK2,k1_xboole_0) | (spl3_1 | ~spl3_3)),
% 0.22/0.47    inference(superposition,[],[f29,f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    k1_xboole_0 = sK0 | ~spl3_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f35])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ~v1_partfun1(sK2,sK0) | spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f28])).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    spl3_9 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f75,f39,f35,f32,f77])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    spl3_2 <=> k1_xboole_0 = sK1),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.22/0.47    inference(forward_demodulation,[],[f72,f70])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    k1_xboole_0 = sK1 | ~spl3_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f32])).
% 0.22/0.47  fof(f72,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl3_3 | ~spl3_4)),
% 0.22/0.47    inference(superposition,[],[f40,f36])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f39])).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    spl3_2 | ~spl3_7 | ~spl3_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f68,f62,f53,f32])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    spl3_8 <=> v1_xboole_0(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    k1_xboole_0 = sK1 | (~spl3_7 | ~spl3_8)),
% 0.22/0.47    inference(resolution,[],[f63,f56])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_7),
% 0.22/0.47    inference(resolution,[],[f26,f54])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    v1_xboole_0(sK1) | ~spl3_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f62])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    spl3_8 | ~spl3_5 | spl3_1 | ~spl3_4 | ~spl3_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f60,f47,f39,f28,f43,f62])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    spl3_5 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    spl3_6 <=> v1_funct_1(sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    v1_partfun1(sK2,sK0) | ~v1_funct_2(sK2,sK0,sK1) | v1_xboole_0(sK1) | (~spl3_4 | ~spl3_6)),
% 0.22/0.47    inference(resolution,[],[f59,f40])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(sK2,X0) | ~v1_funct_2(sK2,X0,X1) | v1_xboole_0(X1)) ) | ~spl3_6),
% 0.22/0.47    inference(resolution,[],[f24,f48])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    v1_funct_1(sK2) | ~spl3_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f47])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.47    inference(flattening,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    spl3_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f22,f53])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    spl3_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f15,f47])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    v1_funct_1(sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ~v1_partfun1(sK2,sK0) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (~v1_partfun1(sK2,sK0) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.22/0.47    inference(flattening,[],[f7])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (((~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.47    inference(negated_conjecture,[],[f5])).
% 0.22/0.47  fof(f5,conjecture,(
% 0.22/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    spl3_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f16,f39])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    spl3_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f18,f43])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ~spl3_2 | spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f20,f35,f32])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ~spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f21,f28])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ~v1_partfun1(sK2,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (31485)------------------------------
% 0.22/0.47  % (31485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (31485)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (31485)Memory used [KB]: 10618
% 0.22/0.47  % (31485)Time elapsed: 0.053 s
% 0.22/0.47  % (31485)------------------------------
% 0.22/0.47  % (31485)------------------------------
% 0.22/0.47  % (31493)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.47  % (31481)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.47  % (31481)Refutation not found, incomplete strategy% (31481)------------------------------
% 0.22/0.47  % (31481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (31481)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (31481)Memory used [KB]: 10490
% 0.22/0.47  % (31481)Time elapsed: 0.060 s
% 0.22/0.47  % (31481)------------------------------
% 0.22/0.47  % (31481)------------------------------
% 0.22/0.48  % (31478)Success in time 0.117 s
%------------------------------------------------------------------------------

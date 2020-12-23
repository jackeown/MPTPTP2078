%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 113 expanded)
%              Number of leaves         :   13 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :  179 ( 356 expanded)
%              Number of equality atoms :   58 ( 117 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f32,f36,f40,f51,f58,f63,f67,f73,f77])).

fof(f77,plain,
    ( spl2_6
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f75,f71,f65,f56])).

fof(f56,plain,
    ( spl2_6
  <=> k1_tarski(sK1) = k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f65,plain,
    ( spl2_8
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f71,plain,
    ( spl2_9
  <=> ! [X0] :
        ( k1_tarski(sK1) = k5_partfun1(k1_xboole_0,X0,k3_partfun1(sK1,k1_xboole_0,X0))
        | ~ v1_funct_2(sK1,k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f75,plain,
    ( k1_tarski(sK1) = k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0))
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(resolution,[],[f72,f66])).

fof(f66,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK1,k1_xboole_0,X0)
        | k1_tarski(sK1) = k5_partfun1(k1_xboole_0,X0,k3_partfun1(sK1,k1_xboole_0,X0)) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f73,plain,
    ( ~ spl2_4
    | spl2_9
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f68,f61,f71,f38])).

fof(f38,plain,
    ( spl2_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f61,plain,
    ( spl2_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f68,plain,
    ( ! [X0] :
        ( k1_tarski(sK1) = k5_partfun1(k1_xboole_0,X0,k3_partfun1(sK1,k1_xboole_0,X0))
        | ~ v1_funct_2(sK1,k1_xboole_0,X0)
        | ~ v1_funct_1(sK1) )
    | ~ spl2_7 ),
    inference(resolution,[],[f62,f41])).

fof(f41,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_tarski(X2) = k5_partfun1(k1_xboole_0,X1,k3_partfun1(X2,k1_xboole_0,X1))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f24,f23])).

fof(f23,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f24,plain,(
    ! [X2,X1] :
      ( k1_tarski(X2) = k5_partfun1(k1_xboole_0,X1,k3_partfun1(X2,k1_xboole_0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_2)).

fof(f62,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f67,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f54,f48,f34,f65])).

fof(f34,plain,
    ( spl2_3
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f48,plain,
    ( spl2_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f54,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f35,f49])).

fof(f49,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f35,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f63,plain,
    ( spl2_7
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f59,f48,f30,f61])).

fof(f30,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f59,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f53,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(superposition,[],[f31,f49])).

fof(f31,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f58,plain,
    ( ~ spl2_6
    | spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f52,f48,f26,f56])).

fof(f26,plain,
    ( spl2_1
  <=> k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f52,plain,
    ( k1_tarski(sK1) != k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0))
    | spl2_1
    | ~ spl2_5 ),
    inference(superposition,[],[f27,f49])).

fof(f27,plain,
    ( k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f51,plain,
    ( spl2_1
    | spl2_5
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f45,f38,f34,f30,f48,f26])).

fof(f45,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0
    | k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_tarski(sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f44,f35])).

fof(f44,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK1,X1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k1_xboole_0 = X0
        | k1_tarski(sK1) = k5_partfun1(X1,X0,k3_partfun1(sK1,X1,X0)) )
    | ~ spl2_4 ),
    inference(resolution,[],[f20,f39])).

fof(f39,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f13,f38])).

fof(f13,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_2)).

fof(f36,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f14,f34])).

fof(f14,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f15,f30])).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f28,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f16,f26])).

fof(f16,plain,(
    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:57:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (27787)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.46  % (27794)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (27788)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (27786)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (27789)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (27795)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (27786)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f28,f32,f36,f40,f51,f58,f63,f67,f73,f77])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    spl2_6 | ~spl2_8 | ~spl2_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f75,f71,f65,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl2_6 <=> k1_tarski(sK1) = k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl2_8 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl2_9 <=> ! [X0] : (k1_tarski(sK1) = k5_partfun1(k1_xboole_0,X0,k3_partfun1(sK1,k1_xboole_0,X0)) | ~v1_funct_2(sK1,k1_xboole_0,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    k1_tarski(sK1) = k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0)) | (~spl2_8 | ~spl2_9)),
% 0.21/0.47    inference(resolution,[],[f72,f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~spl2_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f65])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_funct_2(sK1,k1_xboole_0,X0) | k1_tarski(sK1) = k5_partfun1(k1_xboole_0,X0,k3_partfun1(sK1,k1_xboole_0,X0))) ) | ~spl2_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f71])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ~spl2_4 | spl2_9 | ~spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f68,f61,f71,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    spl2_4 <=> v1_funct_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl2_7 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ( ! [X0] : (k1_tarski(sK1) = k5_partfun1(k1_xboole_0,X0,k3_partfun1(sK1,k1_xboole_0,X0)) | ~v1_funct_2(sK1,k1_xboole_0,X0) | ~v1_funct_1(sK1)) ) | ~spl2_7),
% 0.21/0.47    inference(resolution,[],[f62,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_tarski(X2) = k5_partfun1(k1_xboole_0,X1,k3_partfun1(X2,k1_xboole_0,X1)) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f24,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.47    inference(equality_resolution,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.47    inference(nnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X2,X1] : (k1_tarski(X2) = k5_partfun1(k1_xboole_0,X1,k3_partfun1(X2,k1_xboole_0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.47    inference(equality_resolution,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.47    inference(flattening,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_2)).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | ~spl2_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f61])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl2_8 | ~spl2_3 | ~spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f54,f48,f34,f65])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    spl2_3 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    spl2_5 <=> k1_xboole_0 = sK0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl2_3 | ~spl2_5)),
% 0.21/0.47    inference(superposition,[],[f35,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | ~spl2_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f48])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    v1_funct_2(sK1,sK0,sK0) | ~spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f34])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl2_7 | ~spl2_2 | ~spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f59,f48,f30,f61])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | (~spl2_2 | ~spl2_5)),
% 0.21/0.47    inference(forward_demodulation,[],[f53,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl2_2 | ~spl2_5)),
% 0.21/0.47    inference(superposition,[],[f31,f49])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f30])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ~spl2_6 | spl2_1 | ~spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f52,f48,f26,f56])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    spl2_1 <=> k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_tarski(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    k1_tarski(sK1) != k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0)) | (spl2_1 | ~spl2_5)),
% 0.21/0.47    inference(superposition,[],[f27,f49])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1) | spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f26])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    spl2_1 | spl2_5 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f45,f38,f34,f30,f48,f26])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_tarski(sK1) | (~spl2_3 | ~spl2_4)),
% 0.21/0.47    inference(resolution,[],[f44,f35])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_funct_2(sK1,X1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X0 | k1_tarski(sK1) = k5_partfun1(X1,X0,k3_partfun1(sK1,X1,X0))) ) | ~spl2_4),
% 0.21/0.47    inference(resolution,[],[f20,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    v1_funct_1(sK1) | ~spl2_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f38])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    spl2_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f13,f38])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    v1_funct_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0,X1] : (k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1] : (k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.47    inference(flattening,[],[f5])).
% 0.21/0.47  fof(f5,plain,(
% 0.21/0.47    ? [X0,X1] : (k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f3])).
% 0.21/0.47  fof(f3,conjecture,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_2)).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f14,f34])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f15,f30])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ~spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f16,f26])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (27786)------------------------------
% 0.21/0.47  % (27786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (27786)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (27786)Memory used [KB]: 10618
% 0.21/0.47  % (27786)Time elapsed: 0.006 s
% 0.21/0.47  % (27786)------------------------------
% 0.21/0.47  % (27786)------------------------------
% 0.21/0.48  % (27779)Success in time 0.121 s
%------------------------------------------------------------------------------

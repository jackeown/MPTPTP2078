%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 133 expanded)
%              Number of leaves         :   11 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  153 ( 409 expanded)
%              Number of equality atoms :   46 ( 129 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f60,f62,f64,f68,f69,f78])).

fof(f78,plain,
    ( ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(trivial_inequality_removal,[],[f76])).

fof(f76,plain,
    ( k1_enumset1(sK1,sK1,sK1) != k1_enumset1(sK1,sK1,sK1)
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f71,f59])).

fof(f59,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_6
  <=> k1_enumset1(sK1,sK1,sK1) = k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f71,plain,
    ( k1_enumset1(sK1,sK1,sK1) != k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0))
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f21,f38])).

fof(f38,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl2_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f21,plain,(
    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_enumset1(sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f15,f20])).

fof(f20,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f16,f17])).

fof(f17,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f16,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f15,plain,(
    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).

fof(f10,plain,
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

fof(f7,plain,(
    ? [X0,X1] :
      ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_2)).

fof(f69,plain,
    ( spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f65,f36,f32,f28])).

fof(f28,plain,
    ( spl2_1
  <=> k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_enumset1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f32,plain,
    ( spl2_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f65,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_enumset1(sK1,sK1,sK1) ),
    inference(resolution,[],[f14,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK1,X1,X0)
      | k1_enumset1(sK1,sK1,sK1) = k5_partfun1(X1,X0,k3_partfun1(sK1,X1,X0)) ) ),
    inference(resolution,[],[f23,f12])).

fof(f12,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_enumset1(X2,X2,X2) ) ),
    inference(definition_unfolding,[],[f18,f20])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_2)).

fof(f14,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f68,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f66])).

fof(f66,plain,
    ( k1_enumset1(sK1,sK1,sK1) != k1_enumset1(sK1,sK1,sK1)
    | ~ spl2_1 ),
    inference(superposition,[],[f21,f30])).

fof(f30,plain,
    ( k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_enumset1(sK1,sK1,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f64,plain,
    ( ~ spl2_3
    | spl2_5 ),
    inference(avatar_contradiction_clause,[],[f63])).

fof(f63,plain,
    ( $false
    | ~ spl2_3
    | spl2_5 ),
    inference(resolution,[],[f55,f42])).

fof(f42,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f13,f38])).

fof(f13,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_5
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f62,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | spl2_4 ),
    inference(resolution,[],[f51,f12])).

fof(f51,plain,
    ( ~ v1_funct_1(sK1)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl2_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f60,plain,
    ( ~ spl2_4
    | ~ spl2_5
    | spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f47,f36,f57,f53,f49])).

fof(f47,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0))
    | ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f43,f24])).

fof(f24,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_enumset1(X2,X2,X2) = k5_partfun1(k1_xboole_0,X1,k3_partfun1(X2,k1_xboole_0,X1))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_enumset1(X2,X2,X2)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f14,f38])).

fof(f41,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f40])).

fof(f40,plain,
    ( $false
    | spl2_2 ),
    inference(resolution,[],[f34,f13])).

fof(f34,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (24757)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (24766)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (24766)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f41,f60,f62,f64,f68,f69,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ~spl2_3 | ~spl2_6),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    $false | (~spl2_3 | ~spl2_6)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    k1_enumset1(sK1,sK1,sK1) != k1_enumset1(sK1,sK1,sK1) | (~spl2_3 | ~spl2_6)),
% 0.21/0.51    inference(superposition,[],[f71,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    k1_enumset1(sK1,sK1,sK1) = k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0)) | ~spl2_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    spl2_6 <=> k1_enumset1(sK1,sK1,sK1) = k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    k1_enumset1(sK1,sK1,sK1) != k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0)) | ~spl2_3),
% 0.21/0.51    inference(backward_demodulation,[],[f21,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~spl2_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    spl2_3 <=> k1_xboole_0 = sK0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_enumset1(sK1,sK1,sK1)),
% 0.21/0.51    inference(definition_unfolding,[],[f15,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f16,f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0,X1] : (k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0,X1] : (k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.51    inference(flattening,[],[f6])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ? [X0,X1] : (k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1))),
% 0.21/0.51    inference(negated_conjecture,[],[f4])).
% 0.21/0.51  fof(f4,conjecture,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_2)).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    spl2_1 | ~spl2_2 | spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f65,f36,f32,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    spl2_1 <=> k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_enumset1(sK1,sK1,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    spl2_2 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_enumset1(sK1,sK1,sK1)),
% 0.21/0.51    inference(resolution,[],[f14,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X0 | ~v1_funct_2(sK1,X1,X0) | k1_enumset1(sK1,sK1,sK1) = k5_partfun1(X1,X0,k3_partfun1(sK1,X1,X0))) )),
% 0.21/0.51    inference(resolution,[],[f23,f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    v1_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_enumset1(X2,X2,X2)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f18,f20])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_2)).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ~spl2_1),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    $false | ~spl2_1),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    k1_enumset1(sK1,sK1,sK1) != k1_enumset1(sK1,sK1,sK1) | ~spl2_1),
% 0.21/0.51    inference(superposition,[],[f21,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_enumset1(sK1,sK1,sK1) | ~spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f28])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ~spl2_3 | spl2_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    $false | (~spl2_3 | spl2_5)),
% 0.21/0.51    inference(resolution,[],[f55,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~spl2_3),
% 0.21/0.51    inference(backward_demodulation,[],[f13,f38])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | spl2_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    spl2_5 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl2_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    $false | spl2_4),
% 0.21/0.51    inference(resolution,[],[f51,f12])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ~v1_funct_1(sK1) | spl2_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    spl2_4 <=> v1_funct_1(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ~spl2_4 | ~spl2_5 | spl2_6 | ~spl2_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f47,f36,f57,f53,f49])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    k1_enumset1(sK1,sK1,sK1) = k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0)) | ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK1) | ~spl2_3),
% 0.21/0.52    inference(resolution,[],[f43,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_enumset1(X2,X2,X2) = k5_partfun1(k1_xboole_0,X1,k3_partfun1(X2,k1_xboole_0,X1)) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(equality_resolution,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_enumset1(X2,X2,X2) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f19,f20])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl2_3),
% 0.21/0.52    inference(backward_demodulation,[],[f14,f38])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    spl2_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    $false | spl2_2),
% 0.21/0.52    inference(resolution,[],[f34,f13])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ~v1_funct_2(sK1,sK0,sK0) | spl2_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f32])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (24766)------------------------------
% 0.21/0.52  % (24766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24766)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (24766)Memory used [KB]: 6268
% 0.21/0.52  % (24766)Time elapsed: 0.106 s
% 0.21/0.52  % (24766)------------------------------
% 0.21/0.52  % (24766)------------------------------
% 0.21/0.52  % (24753)Success in time 0.156 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:42:24 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 (  97 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   95 ( 203 expanded)
%              Number of equality atoms :   74 ( 179 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f65,f72])).

fof(f72,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f70,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f70,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl2_1
    | spl2_2 ),
    inference(backward_demodulation,[],[f40,f66])).

fof(f66,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f15,f37,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl2_1
  <=> k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
      | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
          | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
        & k1_xboole_0 != X0 )
   => ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f40,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_2
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f65,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f61,f17])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f61,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f33,f57])).

fof(f57,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f15,f41,f20])).

fof(f41,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f33,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f23,f27,f27,f27])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f19,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f42,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f28,f39,f35])).

fof(f28,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(definition_unfolding,[],[f16,f27,f27])).

fof(f16,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
    | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:57:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.47  % (30364)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.49  % (30380)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.49  % (30380)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f73,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(avatar_sat_refutation,[],[f42,f65,f72])).
% 0.19/0.49  fof(f72,plain,(
% 0.19/0.49    ~spl2_1 | spl2_2),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f71])).
% 0.19/0.49  fof(f71,plain,(
% 0.19/0.49    $false | (~spl2_1 | spl2_2)),
% 0.19/0.49    inference(subsumption_resolution,[],[f70,f31])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.49    inference(equality_resolution,[],[f22])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.49    inference(flattening,[],[f12])).
% 0.19/0.49  fof(f12,plain,(
% 0.19/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.49    inference(nnf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.49  fof(f70,plain,(
% 0.19/0.49    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | (~spl2_1 | spl2_2)),
% 0.19/0.49    inference(backward_demodulation,[],[f40,f66])).
% 0.19/0.49  fof(f66,plain,(
% 0.19/0.49    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl2_1),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f15,f37,f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl2_1),
% 0.19/0.49    inference(avatar_component_clause,[],[f35])).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    spl2_1 <=> k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    k1_xboole_0 != sK0),
% 0.19/0.49    inference(cnf_transformation,[],[f11])).
% 0.19/0.49  fof(f11,plain,(
% 0.19/0.49    (k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.19/0.49  fof(f10,plain,(
% 0.19/0.49    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0) => ((k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0)),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f9,plain,(
% 0.19/0.49    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.19/0.49    inference(ennf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.19/0.49    inference(negated_conjecture,[],[f7])).
% 0.19/0.49  fof(f7,conjecture,(
% 0.19/0.49    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.19/0.49  fof(f40,plain,(
% 0.19/0.49    k1_xboole_0 != k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl2_2),
% 0.19/0.49    inference(avatar_component_clause,[],[f39])).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    spl2_2 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.49  fof(f65,plain,(
% 0.19/0.49    ~spl2_2),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f64])).
% 0.19/0.49  fof(f64,plain,(
% 0.19/0.49    $false | ~spl2_2),
% 0.19/0.49    inference(subsumption_resolution,[],[f61,f17])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.19/0.49  fof(f61,plain,(
% 0.19/0.49    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_2),
% 0.19/0.49    inference(superposition,[],[f33,f57])).
% 0.19/0.49  fof(f57,plain,(
% 0.19/0.49    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl2_2),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f15,f41,f20])).
% 0.19/0.49  fof(f41,plain,(
% 0.19/0.49    k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl2_2),
% 0.19/0.49    inference(avatar_component_clause,[],[f39])).
% 0.19/0.49  fof(f33,plain,(
% 0.19/0.49    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 0.19/0.49    inference(equality_resolution,[],[f30])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 0.19/0.49    inference(definition_unfolding,[],[f23,f27,f27,f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f18,f26])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f19,f25])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  fof(f14,plain,(
% 0.19/0.49    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.19/0.49    inference(nnf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.19/0.49  fof(f42,plain,(
% 0.19/0.49    spl2_1 | spl2_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f28,f39,f35])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.19/0.49    inference(definition_unfolding,[],[f16,f27,f27])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f11])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (30380)------------------------------
% 0.19/0.49  % (30380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (30380)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (30380)Memory used [KB]: 10746
% 0.19/0.49  % (30380)Time elapsed: 0.097 s
% 0.19/0.49  % (30380)------------------------------
% 0.19/0.49  % (30380)------------------------------
% 0.19/0.49  % (30353)Success in time 0.143 s
%------------------------------------------------------------------------------

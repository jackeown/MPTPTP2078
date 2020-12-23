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
% DateTime   : Thu Dec  3 12:42:23 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 156 expanded)
%              Number of leaves         :   12 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  106 ( 259 expanded)
%              Number of equality atoms :   86 ( 237 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f64,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f58,f63])).

fof(f63,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f61,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
      | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
          | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
        & k1_xboole_0 != X0 )
   => ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f61,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f60,f55])).

fof(f55,plain,(
    ! [X1] : k1_xboole_0 != k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(forward_demodulation,[],[f38,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f21,f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f21,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f38,plain,(
    ! [X1] : k3_enumset1(X1,X1,X1,X1,X1) != k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k3_enumset1(X0,X0,X0,X0,X0) != k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f26,f32,f32,f32])).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f22,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f60,plain,
    ( k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f59])).

fof(f59,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | ~ spl2_1 ),
    inference(superposition,[],[f23,f42])).

fof(f42,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_1
  <=> k1_xboole_0 = k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f58,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f57])).

fof(f57,plain,
    ( $false
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f56])).

fof(f56,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl2_2 ),
    inference(superposition,[],[f55,f53])).

fof(f53,plain,
    ( k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f52,f17])).

fof(f52,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f23,f46])).

fof(f46,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_2
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f47,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f33,f44,f40])).

fof(f33,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) ),
    inference(definition_unfolding,[],[f18,f32,f32])).

fof(f18,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
    | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:58:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (811794435)
% 0.13/0.38  ipcrm: permission denied for id (811827208)
% 0.13/0.38  ipcrm: permission denied for id (811859982)
% 0.20/0.40  ipcrm: permission denied for id (811892765)
% 0.20/0.42  ipcrm: permission denied for id (811991096)
% 0.20/0.48  ipcrm: permission denied for id (812056689)
% 0.20/0.49  ipcrm: permission denied for id (812122235)
% 0.70/0.64  % (6479)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.70/0.65  % (6480)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.70/0.65  % (6480)Refutation found. Thanks to Tanya!
% 0.70/0.65  % SZS status Theorem for theBenchmark
% 0.70/0.65  % SZS output start Proof for theBenchmark
% 0.70/0.65  fof(f64,plain,(
% 0.70/0.65    $false),
% 0.70/0.65    inference(avatar_sat_refutation,[],[f47,f58,f63])).
% 0.70/0.65  fof(f63,plain,(
% 0.70/0.65    ~spl2_1),
% 0.70/0.65    inference(avatar_contradiction_clause,[],[f62])).
% 0.70/0.65  fof(f62,plain,(
% 0.70/0.65    $false | ~spl2_1),
% 0.70/0.65    inference(subsumption_resolution,[],[f61,f17])).
% 0.70/0.65  fof(f17,plain,(
% 0.70/0.65    k1_xboole_0 != sK0),
% 0.70/0.65    inference(cnf_transformation,[],[f13])).
% 0.70/0.65  fof(f13,plain,(
% 0.70/0.65    (k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0),
% 0.70/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 0.70/0.65  fof(f12,plain,(
% 0.70/0.65    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0) => ((k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0)),
% 0.70/0.65    introduced(choice_axiom,[])).
% 0.70/0.65  fof(f11,plain,(
% 0.70/0.65    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.70/0.65    inference(ennf_transformation,[],[f10])).
% 0.70/0.65  fof(f10,negated_conjecture,(
% 0.70/0.65    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.70/0.65    inference(negated_conjecture,[],[f9])).
% 0.70/0.65  fof(f9,conjecture,(
% 0.70/0.65    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.70/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.70/0.65  fof(f61,plain,(
% 0.70/0.65    k1_xboole_0 = sK0 | ~spl2_1),
% 0.70/0.65    inference(subsumption_resolution,[],[f60,f55])).
% 0.70/0.65  fof(f55,plain,(
% 0.70/0.65    ( ! [X1] : (k1_xboole_0 != k3_enumset1(X1,X1,X1,X1,X1)) )),
% 0.70/0.65    inference(forward_demodulation,[],[f38,f48])).
% 0.70/0.65  fof(f48,plain,(
% 0.70/0.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.70/0.65    inference(superposition,[],[f21,f19])).
% 0.70/0.65  fof(f19,plain,(
% 0.70/0.65    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.70/0.65    inference(cnf_transformation,[],[f1])).
% 0.70/0.65  fof(f1,axiom,(
% 0.70/0.65    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.70/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.70/0.65  fof(f21,plain,(
% 0.70/0.65    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.70/0.65    inference(cnf_transformation,[],[f2])).
% 0.70/0.65  fof(f2,axiom,(
% 0.70/0.65    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.70/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.70/0.65  fof(f38,plain,(
% 0.70/0.65    ( ! [X1] : (k3_enumset1(X1,X1,X1,X1,X1) != k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1))) )),
% 0.70/0.65    inference(equality_resolution,[],[f35])).
% 0.70/0.65  fof(f35,plain,(
% 0.70/0.65    ( ! [X0,X1] : (X0 != X1 | k3_enumset1(X0,X0,X0,X0,X0) != k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) )),
% 0.70/0.65    inference(definition_unfolding,[],[f26,f32,f32,f32])).
% 0.70/0.65  fof(f32,plain,(
% 0.70/0.65    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.70/0.65    inference(definition_unfolding,[],[f20,f31])).
% 0.70/0.65  fof(f31,plain,(
% 0.70/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.70/0.65    inference(definition_unfolding,[],[f22,f30])).
% 0.70/0.65  fof(f30,plain,(
% 0.70/0.65    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.70/0.65    inference(definition_unfolding,[],[f28,f29])).
% 0.70/0.65  fof(f29,plain,(
% 0.70/0.65    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.70/0.65    inference(cnf_transformation,[],[f6])).
% 0.70/0.65  fof(f6,axiom,(
% 0.70/0.65    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.70/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.70/0.65  fof(f28,plain,(
% 0.70/0.65    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.70/0.65    inference(cnf_transformation,[],[f5])).
% 0.70/0.65  fof(f5,axiom,(
% 0.70/0.65    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.70/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.70/0.65  fof(f22,plain,(
% 0.70/0.65    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.70/0.65    inference(cnf_transformation,[],[f4])).
% 0.70/0.65  fof(f4,axiom,(
% 0.70/0.65    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.70/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.70/0.65  fof(f20,plain,(
% 0.70/0.65    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.70/0.65    inference(cnf_transformation,[],[f3])).
% 0.70/0.65  fof(f3,axiom,(
% 0.70/0.65    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.70/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.70/0.65  fof(f26,plain,(
% 0.70/0.65    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.70/0.65    inference(cnf_transformation,[],[f16])).
% 0.70/0.65  fof(f16,plain,(
% 0.70/0.65    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.70/0.65    inference(nnf_transformation,[],[f8])).
% 0.70/0.65  fof(f8,axiom,(
% 0.70/0.65    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.70/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.70/0.65  fof(f60,plain,(
% 0.70/0.65    k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0 | ~spl2_1),
% 0.70/0.65    inference(trivial_inequality_removal,[],[f59])).
% 0.70/0.65  fof(f59,plain,(
% 0.70/0.65    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0 | ~spl2_1),
% 0.70/0.65    inference(superposition,[],[f23,f42])).
% 0.70/0.65  fof(f42,plain,(
% 0.70/0.65    k1_xboole_0 = k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) | ~spl2_1),
% 0.70/0.65    inference(avatar_component_clause,[],[f40])).
% 0.70/0.65  fof(f40,plain,(
% 0.70/0.65    spl2_1 <=> k1_xboole_0 = k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),
% 0.70/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.70/0.65  fof(f23,plain,(
% 0.70/0.65    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.70/0.65    inference(cnf_transformation,[],[f15])).
% 0.70/0.65  fof(f15,plain,(
% 0.70/0.65    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.70/0.65    inference(flattening,[],[f14])).
% 0.70/0.65  fof(f14,plain,(
% 0.70/0.65    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.70/0.65    inference(nnf_transformation,[],[f7])).
% 0.70/0.65  fof(f7,axiom,(
% 0.70/0.65    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.70/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.70/0.65  fof(f58,plain,(
% 0.70/0.65    ~spl2_2),
% 0.70/0.65    inference(avatar_contradiction_clause,[],[f57])).
% 0.70/0.65  fof(f57,plain,(
% 0.70/0.65    $false | ~spl2_2),
% 0.70/0.65    inference(trivial_inequality_removal,[],[f56])).
% 0.70/0.65  fof(f56,plain,(
% 0.70/0.65    k1_xboole_0 != k1_xboole_0 | ~spl2_2),
% 0.70/0.65    inference(superposition,[],[f55,f53])).
% 0.70/0.65  fof(f53,plain,(
% 0.70/0.65    k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl2_2),
% 0.70/0.65    inference(subsumption_resolution,[],[f52,f17])).
% 0.70/0.65  fof(f52,plain,(
% 0.70/0.65    k1_xboole_0 = sK0 | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl2_2),
% 0.70/0.65    inference(trivial_inequality_removal,[],[f49])).
% 0.70/0.65  fof(f49,plain,(
% 0.70/0.65    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl2_2),
% 0.70/0.65    inference(superposition,[],[f23,f46])).
% 0.70/0.65  fof(f46,plain,(
% 0.70/0.65    k1_xboole_0 = k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl2_2),
% 0.70/0.65    inference(avatar_component_clause,[],[f44])).
% 0.70/0.65  fof(f44,plain,(
% 0.70/0.65    spl2_2 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.70/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.70/0.65  fof(f47,plain,(
% 0.70/0.65    spl2_1 | spl2_2),
% 0.70/0.65    inference(avatar_split_clause,[],[f33,f44,f40])).
% 0.70/0.65  fof(f33,plain,(
% 0.70/0.65    k1_xboole_0 = k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),
% 0.70/0.65    inference(definition_unfolding,[],[f18,f32,f32])).
% 0.70/0.65  fof(f18,plain,(
% 0.70/0.65    k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)),
% 0.70/0.65    inference(cnf_transformation,[],[f13])).
% 0.70/0.65  % SZS output end Proof for theBenchmark
% 0.70/0.65  % (6480)------------------------------
% 0.70/0.65  % (6480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.70/0.65  % (6480)Termination reason: Refutation
% 0.70/0.65  
% 0.70/0.65  % (6480)Memory used [KB]: 10746
% 0.70/0.65  % (6480)Time elapsed: 0.104 s
% 0.70/0.65  % (6480)------------------------------
% 0.70/0.65  % (6480)------------------------------
% 0.70/0.65  % (6478)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.70/0.65  % (6501)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.70/0.65  % (6310)Success in time 0.29 s
%------------------------------------------------------------------------------

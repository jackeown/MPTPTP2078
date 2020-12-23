%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:47 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 135 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :  103 ( 243 expanded)
%              Number of equality atoms :   71 ( 180 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(subsumption_resolution,[],[f82,f42])).

fof(f42,plain,(
    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f18,f41])).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f25,f38])).

% (8811)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (8826)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f18,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f82,plain,(
    sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f81,f61])).

fof(f61,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f60,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,
    ( r2_hidden(sK1,sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f59,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f59,plain,(
    ! [X0] :
      ( r1_tarski(sK0,k4_xboole_0(X0,sK0))
      | r2_hidden(sK1,sK0) ) ),
    inference(superposition,[],[f23,f58])).

fof(f58,plain,(
    ! [X0] : sK1 = sK2(sK0,k4_xboole_0(X0,sK0)) ),
    inference(subsumption_resolution,[],[f57,f19])).

fof(f57,plain,(
    ! [X0] :
      ( sK1 = sK2(sK0,k4_xboole_0(X0,sK0))
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f56,f22])).

fof(f56,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | sK1 = sK2(sK0,X0) ) ),
    inference(resolution,[],[f23,f17])).

fof(f17,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f81,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(trivial_inequality_removal,[],[f78])).

fof(f78,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK1,sK0)
    | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[],[f55,f76])).

fof(f76,plain,(
    sK1 = sK3(sK1,sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,
    ( sK0 != sK0
    | sK1 = sK3(sK1,sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,
    ( sK0 != sK0
    | sK1 = sK3(sK1,sK1,sK0)
    | sK1 = sK3(sK1,sK1,sK0)
    | sK1 = sK3(sK1,sK1,sK0) ),
    inference(superposition,[],[f42,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( sK0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
      | sK3(X0,X1,sK0) = X0
      | sK3(X0,X1,sK0) = X1
      | sK1 = sK3(X0,X1,sK0) ) ),
    inference(resolution,[],[f46,f17])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | sK3(X0,X1,X2) = X1
      | sK3(X0,X1,X2) = X0
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2 ) ),
    inference(definition_unfolding,[],[f28,f40])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) = X0
      | sK3(X0,X1,X2) = X1
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k2_tarski(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) != X0
      | ~ r2_hidden(X0,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2 ) ),
    inference(inner_rewriting,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) != X0
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2 ) ),
    inference(definition_unfolding,[],[f26,f40])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) != X0
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k2_tarski(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (8804)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.48  % (8810)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.49  % (8820)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.49  % (8819)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.49  % (8810)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f83,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(subsumption_resolution,[],[f82,f42])).
% 0.19/0.49  fof(f42,plain,(
% 0.19/0.49    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 0.19/0.49    inference(definition_unfolding,[],[f18,f41])).
% 0.19/0.49  fof(f41,plain,(
% 0.19/0.49    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f20,f40])).
% 0.19/0.49  fof(f40,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f21,f39])).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f25,f38])).
% 0.19/0.49  % (8811)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.51  % (8826)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.51  fof(f38,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f32,f37])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f33,f36])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f34,f35])).
% 0.19/0.51  fof(f35,plain,(
% 0.19/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f10])).
% 0.19/0.51  fof(f10,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f9])).
% 0.19/0.51  fof(f9,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    sK0 != k1_tarski(sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f14])).
% 0.19/0.51  fof(f14,plain,(
% 0.19/0.51    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.19/0.51    inference(ennf_transformation,[],[f12])).
% 0.19/0.51  fof(f12,negated_conjecture,(
% 0.19/0.51    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.19/0.51    inference(negated_conjecture,[],[f11])).
% 0.19/0.51  fof(f11,conjecture,(
% 0.19/0.51    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.19/0.51  fof(f82,plain,(
% 0.19/0.51    sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 0.19/0.51    inference(subsumption_resolution,[],[f81,f61])).
% 0.19/0.51  fof(f61,plain,(
% 0.19/0.51    r2_hidden(sK1,sK0)),
% 0.19/0.51    inference(subsumption_resolution,[],[f60,f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    k1_xboole_0 != sK0),
% 0.19/0.51    inference(cnf_transformation,[],[f14])).
% 0.19/0.51  fof(f60,plain,(
% 0.19/0.51    r2_hidden(sK1,sK0) | k1_xboole_0 = sK0),
% 0.19/0.51    inference(resolution,[],[f59,f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f15,plain,(
% 0.19/0.51    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.19/0.51  fof(f59,plain,(
% 0.19/0.51    ( ! [X0] : (r1_tarski(sK0,k4_xboole_0(X0,sK0)) | r2_hidden(sK1,sK0)) )),
% 0.19/0.51    inference(superposition,[],[f23,f58])).
% 0.19/0.51  fof(f58,plain,(
% 0.19/0.51    ( ! [X0] : (sK1 = sK2(sK0,k4_xboole_0(X0,sK0))) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f57,f19])).
% 0.19/0.51  fof(f57,plain,(
% 0.19/0.51    ( ! [X0] : (sK1 = sK2(sK0,k4_xboole_0(X0,sK0)) | k1_xboole_0 = sK0) )),
% 0.19/0.51    inference(resolution,[],[f56,f22])).
% 0.19/0.51  fof(f56,plain,(
% 0.19/0.51    ( ! [X0] : (r1_tarski(sK0,X0) | sK1 = sK2(sK0,X0)) )),
% 0.19/0.51    inference(resolution,[],[f23,f17])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = X2) )),
% 0.19/0.51    inference(cnf_transformation,[],[f14])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f16])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f13])).
% 0.19/0.51  fof(f13,plain,(
% 0.19/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.19/0.51    inference(unused_predicate_definition_removal,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.51  fof(f81,plain,(
% 0.19/0.51    ~r2_hidden(sK1,sK0) | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 0.19/0.51    inference(trivial_inequality_removal,[],[f78])).
% 0.19/0.51  fof(f78,plain,(
% 0.19/0.51    sK1 != sK1 | ~r2_hidden(sK1,sK0) | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 0.19/0.51    inference(superposition,[],[f55,f76])).
% 0.19/0.51  fof(f76,plain,(
% 0.19/0.51    sK1 = sK3(sK1,sK1,sK0)),
% 0.19/0.51    inference(trivial_inequality_removal,[],[f75])).
% 0.19/0.51  fof(f75,plain,(
% 0.19/0.51    sK0 != sK0 | sK1 = sK3(sK1,sK1,sK0)),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f71])).
% 0.19/0.51  fof(f71,plain,(
% 0.19/0.51    sK0 != sK0 | sK1 = sK3(sK1,sK1,sK0) | sK1 = sK3(sK1,sK1,sK0) | sK1 = sK3(sK1,sK1,sK0)),
% 0.19/0.51    inference(superposition,[],[f42,f69])).
% 0.19/0.51  fof(f69,plain,(
% 0.19/0.51    ( ! [X0,X1] : (sK0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) | sK3(X0,X1,sK0) = X0 | sK3(X0,X1,sK0) = X1 | sK1 = sK3(X0,X1,sK0)) )),
% 0.19/0.51    inference(resolution,[],[f46,f17])).
% 0.19/0.51  fof(f46,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2) )),
% 0.19/0.51    inference(definition_unfolding,[],[f28,f40])).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (sK3(X0,X1,X2) = X0 | sK3(X0,X1,X2) = X1 | r2_hidden(sK3(X0,X1,X2),X2) | k2_tarski(X0,X1) = X2) )),
% 0.19/0.51    inference(cnf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.19/0.51  fof(f55,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (sK3(X0,X1,X2) != X0 | ~r2_hidden(X0,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2) )),
% 0.19/0.51    inference(inner_rewriting,[],[f48])).
% 0.19/0.51  fof(f48,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (sK3(X0,X1,X2) != X0 | ~r2_hidden(sK3(X0,X1,X2),X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2) )),
% 0.19/0.51    inference(definition_unfolding,[],[f26,f40])).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (sK3(X0,X1,X2) != X0 | ~r2_hidden(sK3(X0,X1,X2),X2) | k2_tarski(X0,X1) = X2) )),
% 0.19/0.51    inference(cnf_transformation,[],[f3])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (8810)------------------------------
% 0.19/0.51  % (8810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (8810)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (8810)Memory used [KB]: 6268
% 0.19/0.51  % (8810)Time elapsed: 0.089 s
% 0.19/0.51  % (8810)------------------------------
% 0.19/0.51  % (8810)------------------------------
% 0.19/0.51  % (8803)Success in time 0.155 s
%------------------------------------------------------------------------------

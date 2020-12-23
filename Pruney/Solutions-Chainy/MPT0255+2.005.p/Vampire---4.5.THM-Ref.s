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
% DateTime   : Thu Dec  3 12:39:34 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 110 expanded)
%              Number of leaves         :   17 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  170 ( 219 expanded)
%              Number of equality atoms :   81 ( 126 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(subsumption_resolution,[],[f161,f82])).

fof(f82,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f81,f40])).

fof(f40,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f47,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f161,plain,(
    r2_hidden(sK1,k1_xboole_0) ),
    inference(superposition,[],[f88,f142])).

fof(f142,plain,(
    k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK2) ),
    inference(resolution,[],[f136,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f52,f38])).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f136,plain,(
    v1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f133,f38])).

fof(f133,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(superposition,[],[f69,f130])).

fof(f130,plain,(
    k1_xboole_0 = k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK1,sK1,sK1,sK1,sK2))) ),
    inference(forward_demodulation,[],[f66,f68])).

fof(f68,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f43,f64,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f66,plain,(
    k1_xboole_0 = k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f37,f65,f64])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f64])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f48,f65])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).

fof(f88,plain,(
    ! [X0,X1] : r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(resolution,[],[f76,f75])).

fof(f75,plain,(
    ! [X4,X2,X0] :
      ( ~ sP0(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK5(X0,X1,X2) != X0
              & sK5(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X0
            | sK5(X0,X1,X2) = X1
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X0
            & sK5(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X0
          | sK5(X0,X1,X2) = X1
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f76,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f60,f64])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f11,f23])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:20:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (810942464)
% 0.13/0.37  ipcrm: permission denied for id (811008003)
% 0.13/0.38  ipcrm: permission denied for id (811073544)
% 0.13/0.38  ipcrm: permission denied for id (811106315)
% 0.13/0.38  ipcrm: permission denied for id (811171855)
% 0.13/0.39  ipcrm: permission denied for id (811368471)
% 0.13/0.40  ipcrm: permission denied for id (811401247)
% 0.13/0.41  ipcrm: permission denied for id (811499558)
% 0.13/0.42  ipcrm: permission denied for id (811565097)
% 0.13/0.42  ipcrm: permission denied for id (811630635)
% 0.13/0.43  ipcrm: permission denied for id (811663408)
% 0.22/0.43  ipcrm: permission denied for id (811696178)
% 0.22/0.43  ipcrm: permission denied for id (811794486)
% 0.22/0.45  ipcrm: permission denied for id (811925570)
% 0.22/0.46  ipcrm: permission denied for id (812023878)
% 0.22/0.46  ipcrm: permission denied for id (812089416)
% 0.22/0.47  ipcrm: permission denied for id (812154961)
% 0.22/0.49  ipcrm: permission denied for id (812286044)
% 0.22/0.49  ipcrm: permission denied for id (812318813)
% 0.22/0.49  ipcrm: permission denied for id (812351582)
% 0.22/0.51  ipcrm: permission denied for id (812515436)
% 0.22/0.52  ipcrm: permission denied for id (812548209)
% 0.22/0.52  ipcrm: permission denied for id (812679286)
% 0.22/0.53  ipcrm: permission denied for id (812777596)
% 0.48/0.62  % (31964)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.86/0.64  % (31955)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.02/0.65  % (31955)Refutation not found, incomplete strategy% (31955)------------------------------
% 1.02/0.65  % (31955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.02/0.65  % (31955)Termination reason: Refutation not found, incomplete strategy
% 1.02/0.65  
% 1.02/0.65  % (31955)Memory used [KB]: 1663
% 1.02/0.65  % (31955)Time elapsed: 0.056 s
% 1.02/0.65  % (31955)------------------------------
% 1.02/0.65  % (31955)------------------------------
% 1.02/0.65  % (31968)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.02/0.65  % (31960)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.02/0.66  % (31960)Refutation found. Thanks to Tanya!
% 1.02/0.66  % SZS status Theorem for theBenchmark
% 1.02/0.66  % SZS output start Proof for theBenchmark
% 1.02/0.66  fof(f176,plain,(
% 1.02/0.66    $false),
% 1.02/0.66    inference(subsumption_resolution,[],[f161,f82])).
% 1.02/0.66  fof(f82,plain,(
% 1.02/0.66    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.02/0.66    inference(subsumption_resolution,[],[f81,f40])).
% 1.02/0.66  fof(f40,plain,(
% 1.02/0.66    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.02/0.66    inference(cnf_transformation,[],[f7])).
% 1.02/0.66  fof(f7,axiom,(
% 1.02/0.66    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.02/0.66  fof(f81,plain,(
% 1.02/0.66    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 1.02/0.66    inference(superposition,[],[f47,f41])).
% 1.02/0.66  fof(f41,plain,(
% 1.02/0.66    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.02/0.66    inference(cnf_transformation,[],[f5])).
% 1.02/0.66  fof(f5,axiom,(
% 1.02/0.66    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.02/0.66  fof(f47,plain,(
% 1.02/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.02/0.66    inference(cnf_transformation,[],[f28])).
% 1.02/0.66  fof(f28,plain,(
% 1.02/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.02/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f27])).
% 1.02/0.66  fof(f27,plain,(
% 1.02/0.66    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.02/0.66    introduced(choice_axiom,[])).
% 1.02/0.66  fof(f20,plain,(
% 1.02/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.02/0.66    inference(ennf_transformation,[],[f18])).
% 1.02/0.66  fof(f18,plain,(
% 1.02/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.02/0.66    inference(rectify,[],[f2])).
% 1.02/0.66  fof(f2,axiom,(
% 1.02/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.02/0.66  fof(f161,plain,(
% 1.02/0.66    r2_hidden(sK1,k1_xboole_0)),
% 1.02/0.66    inference(superposition,[],[f88,f142])).
% 1.02/0.66  fof(f142,plain,(
% 1.02/0.66    k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK2)),
% 1.02/0.66    inference(resolution,[],[f136,f79])).
% 1.02/0.66  fof(f79,plain,(
% 1.02/0.66    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.02/0.66    inference(resolution,[],[f52,f38])).
% 1.02/0.66  fof(f38,plain,(
% 1.02/0.66    v1_xboole_0(k1_xboole_0)),
% 1.02/0.66    inference(cnf_transformation,[],[f1])).
% 1.02/0.66  fof(f1,axiom,(
% 1.02/0.66    v1_xboole_0(k1_xboole_0)),
% 1.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.02/0.66  fof(f52,plain,(
% 1.02/0.66    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.02/0.66    inference(cnf_transformation,[],[f22])).
% 1.02/0.66  fof(f22,plain,(
% 1.02/0.66    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.02/0.66    inference(ennf_transformation,[],[f9])).
% 1.02/0.67  fof(f9,axiom,(
% 1.02/0.67    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.02/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 1.02/0.67  fof(f136,plain,(
% 1.02/0.67    v1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.02/0.67    inference(subsumption_resolution,[],[f133,f38])).
% 1.02/0.67  fof(f133,plain,(
% 1.02/0.67    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.02/0.67    inference(superposition,[],[f69,f130])).
% 1.02/0.67  fof(f130,plain,(
% 1.02/0.67    k1_xboole_0 = k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK1,sK1,sK1,sK1,sK2)))),
% 1.02/0.67    inference(forward_demodulation,[],[f66,f68])).
% 1.02/0.67  fof(f68,plain,(
% 1.02/0.67    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 1.02/0.67    inference(definition_unfolding,[],[f43,f64,f64])).
% 1.02/0.67  fof(f64,plain,(
% 1.02/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.02/0.67    inference(definition_unfolding,[],[f45,f63])).
% 1.02/0.67  fof(f63,plain,(
% 1.02/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.02/0.67    inference(definition_unfolding,[],[f53,f62])).
% 1.02/0.67  fof(f62,plain,(
% 1.02/0.67    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.02/0.67    inference(cnf_transformation,[],[f14])).
% 1.02/0.67  fof(f14,axiom,(
% 1.02/0.67    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.02/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.02/0.67  fof(f53,plain,(
% 1.02/0.67    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.02/0.67    inference(cnf_transformation,[],[f13])).
% 1.02/0.67  fof(f13,axiom,(
% 1.02/0.67    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.02/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.02/0.67  fof(f45,plain,(
% 1.02/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.02/0.67    inference(cnf_transformation,[],[f12])).
% 1.02/0.67  fof(f12,axiom,(
% 1.02/0.67    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.02/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.02/0.67  fof(f43,plain,(
% 1.02/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.02/0.67    inference(cnf_transformation,[],[f10])).
% 1.02/0.67  fof(f10,axiom,(
% 1.02/0.67    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.02/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.02/0.67  fof(f66,plain,(
% 1.02/0.67    k1_xboole_0 = k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3))),
% 1.02/0.67    inference(definition_unfolding,[],[f37,f65,f64])).
% 1.02/0.67  fof(f65,plain,(
% 1.02/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.02/0.67    inference(definition_unfolding,[],[f44,f64])).
% 1.02/0.67  fof(f44,plain,(
% 1.02/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.02/0.67    inference(cnf_transformation,[],[f15])).
% 1.02/0.67  fof(f15,axiom,(
% 1.02/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.02/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.02/0.67  fof(f37,plain,(
% 1.02/0.67    k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 1.02/0.67    inference(cnf_transformation,[],[f26])).
% 1.02/0.67  fof(f26,plain,(
% 1.02/0.67    k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 1.02/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f25])).
% 1.02/0.67  fof(f25,plain,(
% 1.02/0.67    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 1.02/0.67    introduced(choice_axiom,[])).
% 1.02/0.67  fof(f19,plain,(
% 1.02/0.67    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.02/0.67    inference(ennf_transformation,[],[f17])).
% 1.02/0.67  fof(f17,negated_conjecture,(
% 1.02/0.67    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.02/0.67    inference(negated_conjecture,[],[f16])).
% 1.02/0.67  fof(f16,conjecture,(
% 1.02/0.67    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.02/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 1.02/0.67  fof(f69,plain,(
% 1.02/0.67    ( ! [X0,X1] : (~v1_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) | v1_xboole_0(X0)) )),
% 1.02/0.67    inference(definition_unfolding,[],[f48,f65])).
% 1.02/0.67  fof(f48,plain,(
% 1.02/0.67    ( ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X1,X0)) | v1_xboole_0(X0)) )),
% 1.02/0.67    inference(cnf_transformation,[],[f21])).
% 1.02/0.67  fof(f21,plain,(
% 1.02/0.67    ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X1,X0)) | v1_xboole_0(X0))),
% 1.02/0.67    inference(ennf_transformation,[],[f4])).
% 1.02/0.67  fof(f4,axiom,(
% 1.02/0.67    ! [X0,X1] : (~v1_xboole_0(X0) => ~v1_xboole_0(k2_xboole_0(X1,X0)))),
% 1.02/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).
% 1.02/0.67  fof(f88,plain,(
% 1.02/0.67    ( ! [X0,X1] : (r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.02/0.67    inference(resolution,[],[f76,f75])).
% 1.02/0.67  fof(f75,plain,(
% 1.02/0.67    ( ! [X4,X2,X0] : (~sP0(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 1.02/0.67    inference(equality_resolution,[],[f55])).
% 1.02/0.67  fof(f55,plain,(
% 1.02/0.67    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP0(X0,X1,X2)) )),
% 1.02/0.67    inference(cnf_transformation,[],[f35])).
% 1.02/0.67  fof(f35,plain,(
% 1.02/0.67    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK5(X0,X1,X2) != X0 & sK5(X0,X1,X2) != X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X0 | sK5(X0,X1,X2) = X1 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.02/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).
% 1.02/0.67  fof(f34,plain,(
% 1.02/0.67    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X0 & sK5(X0,X1,X2) != X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X0 | sK5(X0,X1,X2) = X1 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.02/0.67    introduced(choice_axiom,[])).
% 1.02/0.67  fof(f33,plain,(
% 1.02/0.67    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.02/0.67    inference(rectify,[],[f32])).
% 1.02/0.67  fof(f32,plain,(
% 1.02/0.67    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.02/0.67    inference(flattening,[],[f31])).
% 1.02/0.67  fof(f31,plain,(
% 1.02/0.67    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.02/0.67    inference(nnf_transformation,[],[f23])).
% 1.02/0.67  fof(f23,plain,(
% 1.02/0.67    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.02/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.02/0.67  fof(f76,plain,(
% 1.02/0.67    ( ! [X0,X1] : (sP0(X1,X0,k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.02/0.67    inference(equality_resolution,[],[f71])).
% 1.02/0.67  fof(f71,plain,(
% 1.02/0.67    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 1.02/0.67    inference(definition_unfolding,[],[f60,f64])).
% 1.02/0.67  fof(f60,plain,(
% 1.02/0.67    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.02/0.67    inference(cnf_transformation,[],[f36])).
% 1.02/0.67  fof(f36,plain,(
% 1.02/0.67    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.02/0.67    inference(nnf_transformation,[],[f24])).
% 1.02/0.67  fof(f24,plain,(
% 1.02/0.67    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.02/0.67    inference(definition_folding,[],[f11,f23])).
% 1.02/0.67  fof(f11,axiom,(
% 1.02/0.67    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.02/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.02/0.67  % SZS output end Proof for theBenchmark
% 1.02/0.67  % (31960)------------------------------
% 1.02/0.67  % (31960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.02/0.67  % (31960)Termination reason: Refutation
% 1.02/0.67  
% 1.02/0.67  % (31960)Memory used [KB]: 10746
% 1.02/0.67  % (31960)Time elapsed: 0.080 s
% 1.02/0.67  % (31960)------------------------------
% 1.02/0.67  % (31960)------------------------------
% 1.02/0.67  % (31974)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.02/0.67  % (31795)Success in time 0.306 s
%------------------------------------------------------------------------------

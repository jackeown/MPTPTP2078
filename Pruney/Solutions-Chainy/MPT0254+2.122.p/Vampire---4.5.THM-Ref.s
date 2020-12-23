%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 108 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  173 ( 216 expanded)
%              Number of equality atoms :   93 ( 134 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(subsumption_resolution,[],[f158,f110])).

fof(f110,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f81,f41])).

fof(f41,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f72])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f158,plain,(
    r2_hidden(sK1,k1_xboole_0) ),
    inference(superposition,[],[f108,f150])).

fof(f150,plain,(
    k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(resolution,[],[f145,f102])).

fof(f102,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f100,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f100,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f97])).

fof(f97,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f80,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f47])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f145,plain,(
    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) ),
    inference(superposition,[],[f120,f141])).

fof(f141,plain,(
    k1_xboole_0 = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f74,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f66,f67,f67])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(f74,plain,(
    k1_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) ),
    inference(definition_unfolding,[],[f39,f70,f72])).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f39,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f28])).

fof(f28,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f120,plain,(
    ! [X8,X9] : r1_tarski(X8,k3_tarski(k5_enumset1(X9,X9,X9,X9,X8,X8,X8))) ),
    inference(superposition,[],[f76,f84])).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f70])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f108,plain,(
    ! [X2,X3] : r2_hidden(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X2)) ),
    inference(resolution,[],[f89,f87])).

fof(f87,plain,(
    ! [X4,X2,X1] :
      ( ~ sP0(X4,X1,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK3(X0,X1,X2) != X0
              & sK3(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X0
            | sK3(X0,X1,X2) = X1
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X0
            & sK3(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X0
          | sK3(X0,X1,X2) = X1
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f89,plain,(
    ! [X0,X1] : sP0(X1,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f64,f69])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f10,f26])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:44:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.58  % (29924)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.58  % (29941)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.59  % (29933)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.59  % (29924)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f169,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(subsumption_resolution,[],[f158,f110])).
% 0.22/0.59  fof(f110,plain,(
% 0.22/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.59    inference(resolution,[],[f81,f41])).
% 0.22/0.59  fof(f41,plain,(
% 0.22/0.59    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,axiom,(
% 0.22/0.59    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.59  fof(f81,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.59    inference(definition_unfolding,[],[f56,f72])).
% 0.22/0.59  fof(f72,plain,(
% 0.22/0.59    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.59    inference(definition_unfolding,[],[f43,f69])).
% 0.22/0.59  fof(f69,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.59    inference(definition_unfolding,[],[f48,f67])).
% 0.22/0.59  fof(f67,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f16])).
% 0.22/0.59  fof(f16,axiom,(
% 0.22/0.59    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_enumset1)).
% 0.22/0.59  fof(f48,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f15])).
% 0.22/0.59  fof(f15,axiom,(
% 0.22/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 0.22/0.59  fof(f43,plain,(
% 0.22/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f13])).
% 0.22/0.59  fof(f13,axiom,(
% 0.22/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.59  fof(f56,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f25])).
% 0.22/0.59  fof(f25,plain,(
% 0.22/0.59    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f17])).
% 0.22/0.59  fof(f17,axiom,(
% 0.22/0.59    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.22/0.59  fof(f158,plain,(
% 0.22/0.59    r2_hidden(sK1,k1_xboole_0)),
% 0.22/0.59    inference(superposition,[],[f108,f150])).
% 0.22/0.59  fof(f150,plain,(
% 0.22/0.59    k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 0.22/0.59    inference(resolution,[],[f145,f102])).
% 0.22/0.59  fof(f102,plain,(
% 0.22/0.59    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 0.22/0.59    inference(resolution,[],[f100,f53])).
% 0.22/0.59  fof(f53,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f31])).
% 0.22/0.59  fof(f31,plain,(
% 0.22/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.59    inference(flattening,[],[f30])).
% 0.22/0.59  fof(f30,plain,(
% 0.22/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.59    inference(nnf_transformation,[],[f3])).
% 0.22/0.59  fof(f3,axiom,(
% 0.22/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.59  fof(f100,plain,(
% 0.22/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.59    inference(trivial_inequality_removal,[],[f97])).
% 0.22/0.59  fof(f97,plain,(
% 0.22/0.59    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.59    inference(superposition,[],[f80,f75])).
% 0.22/0.59  fof(f75,plain,(
% 0.22/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 0.22/0.59    inference(definition_unfolding,[],[f42,f47])).
% 0.22/0.59  fof(f47,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f6])).
% 0.22/0.59  fof(f6,axiom,(
% 0.22/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.59  fof(f42,plain,(
% 0.22/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f7])).
% 0.22/0.59  fof(f7,axiom,(
% 0.22/0.59    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.59  fof(f80,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(definition_unfolding,[],[f54,f47])).
% 0.22/0.59  fof(f54,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f32])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.22/0.59    inference(nnf_transformation,[],[f5])).
% 0.22/0.59  fof(f5,axiom,(
% 0.22/0.59    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.59  fof(f145,plain,(
% 0.22/0.59    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)),
% 0.22/0.59    inference(superposition,[],[f120,f141])).
% 0.22/0.59  fof(f141,plain,(
% 0.22/0.59    k1_xboole_0 = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 0.22/0.59    inference(forward_demodulation,[],[f74,f84])).
% 0.22/0.59  fof(f84,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0)) )),
% 0.22/0.59    inference(definition_unfolding,[],[f66,f67,f67])).
% 0.22/0.59  fof(f66,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f12])).
% 0.22/0.59  fof(f12,axiom,(
% 0.22/0.59    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 0.22/0.59  fof(f74,plain,(
% 0.22/0.59    k1_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))),
% 0.22/0.59    inference(definition_unfolding,[],[f39,f70,f72])).
% 0.22/0.59  fof(f70,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.59    inference(definition_unfolding,[],[f46,f69])).
% 0.22/0.59  fof(f46,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f18])).
% 0.22/0.59  fof(f18,axiom,(
% 0.22/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 0.22/0.59    inference(cnf_transformation,[],[f29])).
% 0.22/0.59  fof(f29,plain,(
% 0.22/0.59    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f28])).
% 0.22/0.59  fof(f28,plain,(
% 0.22/0.59    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f22,plain,(
% 0.22/0.59    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.59    inference(ennf_transformation,[],[f21])).
% 0.22/0.59  fof(f21,negated_conjecture,(
% 0.22/0.59    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.59    inference(negated_conjecture,[],[f20])).
% 0.22/0.59  fof(f20,conjecture,(
% 0.22/0.59    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.59  fof(f120,plain,(
% 0.22/0.59    ( ! [X8,X9] : (r1_tarski(X8,k3_tarski(k5_enumset1(X9,X9,X9,X9,X8,X8,X8)))) )),
% 0.22/0.59    inference(superposition,[],[f76,f84])).
% 0.22/0.59  fof(f76,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.22/0.59    inference(definition_unfolding,[],[f45,f70])).
% 0.22/0.59  fof(f45,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f9])).
% 0.22/0.59  fof(f9,axiom,(
% 0.22/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.59  fof(f108,plain,(
% 0.22/0.59    ( ! [X2,X3] : (r2_hidden(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X2))) )),
% 0.22/0.59    inference(resolution,[],[f89,f87])).
% 0.22/0.59  fof(f87,plain,(
% 0.22/0.59    ( ! [X4,X2,X1] : (~sP0(X4,X1,X2) | r2_hidden(X4,X2)) )),
% 0.22/0.59    inference(equality_resolution,[],[f60])).
% 0.22/0.59  fof(f60,plain,(
% 0.22/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | ~sP0(X0,X1,X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f37])).
% 0.22/0.59  fof(f37,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK3(X0,X1,X2) != X0 & sK3(X0,X1,X2) != X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X0 | sK3(X0,X1,X2) = X1 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 0.22/0.59  fof(f36,plain,(
% 0.22/0.59    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X0 & sK3(X0,X1,X2) != X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X0 | sK3(X0,X1,X2) = X1 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f35,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.59    inference(rectify,[],[f34])).
% 0.22/0.59  fof(f34,plain,(
% 0.22/0.59    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.59    inference(flattening,[],[f33])).
% 0.22/0.59  fof(f33,plain,(
% 0.22/0.59    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.59    inference(nnf_transformation,[],[f26])).
% 0.22/0.59  fof(f26,plain,(
% 0.22/0.59    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.59  fof(f89,plain,(
% 0.22/0.59    ( ! [X0,X1] : (sP0(X1,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.59    inference(equality_resolution,[],[f83])).
% 0.22/0.59  fof(f83,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 0.22/0.59    inference(definition_unfolding,[],[f64,f69])).
% 0.22/0.59  fof(f64,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.59    inference(cnf_transformation,[],[f38])).
% 0.22/0.59  fof(f38,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.22/0.59    inference(nnf_transformation,[],[f27])).
% 0.22/0.59  fof(f27,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.22/0.59    inference(definition_folding,[],[f10,f26])).
% 0.22/0.59  fof(f10,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (29924)------------------------------
% 0.22/0.59  % (29924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (29924)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (29924)Memory used [KB]: 10746
% 0.22/0.59  % (29924)Time elapsed: 0.150 s
% 0.22/0.59  % (29924)------------------------------
% 0.22/0.59  % (29924)------------------------------
% 0.22/0.59  % (29917)Success in time 0.226 s
%------------------------------------------------------------------------------

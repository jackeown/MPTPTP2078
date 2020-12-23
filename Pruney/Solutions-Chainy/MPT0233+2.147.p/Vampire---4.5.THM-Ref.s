%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 164 expanded)
%              Number of leaves         :   16 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  209 ( 329 expanded)
%              Number of equality atoms :  141 ( 249 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f292,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f291])).

fof(f291,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f33,f257])).

fof(f257,plain,(
    sK0 = sK2 ),
    inference(trivial_inequality_removal,[],[f244])).

fof(f244,plain,
    ( sK0 != sK0
    | sK0 = sK2 ),
    inference(superposition,[],[f34,f238])).

fof(f238,plain,
    ( sK0 = sK3
    | sK0 = sK2 ),
    inference(trivial_inequality_removal,[],[f236])).

fof(f236,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 = sK2
    | sK0 = sK3 ),
    inference(superposition,[],[f124,f203])).

fof(f203,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK0 = sK2
    | sK0 = sK3 ),
    inference(superposition,[],[f115,f99])).

fof(f99,plain,(
    k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK2,sK2,sK2,sK2,sK3)) ),
    inference(resolution,[],[f89,f62])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f60,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f59])).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f89,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
      | k1_xboole_0 = k4_xboole_0(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK3)) ) ),
    inference(resolution,[],[f88,f61])).

fof(f61,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f32,f59,f59])).

fof(f32,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X0)
      | k1_xboole_0 = k4_xboole_0(X2,X1) ) ),
    inference(resolution,[],[f35,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2))
      | X0 = X1
      | X0 = X2 ) ),
    inference(resolution,[],[f76,f81])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f43,f59])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f76,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,X2)
      | k3_enumset1(X1,X1,X1,X1,X1) = k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f42,f60,f59])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f124,plain,(
    ! [X1] : k1_xboole_0 != k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(forward_demodulation,[],[f82,f85])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f73,f51])).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f52,f55])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f82,plain,(
    ! [X1] : k3_enumset1(X1,X1,X1,X1,X1) != k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k3_enumset1(X0,X0,X0,X0,X0) != k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f53,f60,f60,f60])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f34,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:27:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (25038)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.50  % (25021)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (25021)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (25029)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f292,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f291])).
% 0.20/0.52  fof(f291,plain,(
% 0.20/0.52    sK0 != sK0),
% 0.20/0.52    inference(superposition,[],[f33,f257])).
% 0.20/0.52  fof(f257,plain,(
% 0.20/0.52    sK0 = sK2),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f244])).
% 0.20/0.52  fof(f244,plain,(
% 0.20/0.52    sK0 != sK0 | sK0 = sK2),
% 0.20/0.52    inference(superposition,[],[f34,f238])).
% 0.20/0.52  fof(f238,plain,(
% 0.20/0.52    sK0 = sK3 | sK0 = sK2),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f236])).
% 0.20/0.52  fof(f236,plain,(
% 0.20/0.52    k1_xboole_0 != k1_xboole_0 | sK0 = sK2 | sK0 = sK3),
% 0.20/0.52    inference(superposition,[],[f124,f203])).
% 0.20/0.52  fof(f203,plain,(
% 0.20/0.52    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK0 = sK2 | sK0 = sK3),
% 0.20/0.52    inference(superposition,[],[f115,f99])).
% 1.26/0.52  fof(f99,plain,(
% 1.26/0.52    k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK2,sK2,sK2,sK2,sK3))),
% 1.26/0.52    inference(resolution,[],[f89,f62])).
% 1.26/0.52  fof(f62,plain,(
% 1.26/0.52    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.26/0.52    inference(definition_unfolding,[],[f38,f60,f59])).
% 1.26/0.52  fof(f59,plain,(
% 1.26/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.26/0.52    inference(definition_unfolding,[],[f49,f58])).
% 1.26/0.52  fof(f58,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.26/0.52    inference(definition_unfolding,[],[f56,f57])).
% 1.26/0.52  fof(f57,plain,(
% 1.26/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f10])).
% 1.26/0.52  fof(f10,axiom,(
% 1.26/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.26/0.52  fof(f56,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f9])).
% 1.26/0.52  fof(f9,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.26/0.52  fof(f49,plain,(
% 1.26/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f8])).
% 1.26/0.52  fof(f8,axiom,(
% 1.26/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.26/0.52  fof(f60,plain,(
% 1.26/0.52    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.26/0.52    inference(definition_unfolding,[],[f50,f59])).
% 1.26/0.52  fof(f50,plain,(
% 1.26/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f7])).
% 1.26/0.52  fof(f7,axiom,(
% 1.26/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.26/0.52  fof(f38,plain,(
% 1.26/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f14])).
% 1.26/0.52  fof(f14,axiom,(
% 1.26/0.52    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.26/0.52  fof(f89,plain,(
% 1.26/0.52    ( ! [X0] : (~r1_tarski(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | k1_xboole_0 = k4_xboole_0(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK3))) )),
% 1.26/0.52    inference(resolution,[],[f88,f61])).
% 1.26/0.52  fof(f61,plain,(
% 1.26/0.52    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3))),
% 1.26/0.52    inference(definition_unfolding,[],[f32,f59,f59])).
% 1.26/0.52  fof(f32,plain,(
% 1.26/0.52    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.26/0.52    inference(cnf_transformation,[],[f22])).
% 1.26/0.52  fof(f22,plain,(
% 1.26/0.52    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.26/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f21])).
% 1.26/0.52  fof(f21,plain,(
% 1.26/0.52    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f18,plain,(
% 1.26/0.52    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.26/0.52    inference(ennf_transformation,[],[f17])).
% 1.26/0.52  fof(f17,negated_conjecture,(
% 1.26/0.52    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.26/0.52    inference(negated_conjecture,[],[f16])).
% 1.26/0.52  fof(f16,conjecture,(
% 1.26/0.52    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.26/0.52  fof(f88,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X0) | k1_xboole_0 = k4_xboole_0(X2,X1)) )),
% 1.26/0.52    inference(resolution,[],[f35,f37])).
% 1.26/0.52  fof(f37,plain,(
% 1.26/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.26/0.52    inference(cnf_transformation,[],[f23])).
% 1.26/0.52  fof(f23,plain,(
% 1.26/0.52    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.26/0.52    inference(nnf_transformation,[],[f1])).
% 1.26/0.52  fof(f1,axiom,(
% 1.26/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.26/0.52  fof(f35,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f20])).
% 1.26/0.52  fof(f20,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.26/0.52    inference(flattening,[],[f19])).
% 1.26/0.52  fof(f19,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.26/0.52    inference(ennf_transformation,[],[f2])).
% 1.26/0.52  fof(f2,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.26/0.52  fof(f115,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) | X0 = X1 | X0 = X2) )),
% 1.26/0.52    inference(resolution,[],[f76,f81])).
% 1.26/0.52  fof(f81,plain,(
% 1.26/0.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 1.26/0.52    inference(equality_resolution,[],[f72])).
% 1.26/0.52  fof(f72,plain,(
% 1.26/0.52    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 1.26/0.52    inference(definition_unfolding,[],[f43,f59])).
% 1.26/0.52  fof(f43,plain,(
% 1.26/0.52    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.26/0.52    inference(cnf_transformation,[],[f30])).
% 1.26/0.52  fof(f30,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.26/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 1.26/0.52  fof(f29,plain,(
% 1.26/0.52    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f28,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.26/0.52    inference(rectify,[],[f27])).
% 1.26/0.52  fof(f27,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.26/0.52    inference(flattening,[],[f26])).
% 1.26/0.52  fof(f26,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.26/0.52    inference(nnf_transformation,[],[f6])).
% 1.26/0.52  fof(f6,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.26/0.52  fof(f76,plain,(
% 1.26/0.52    ( ! [X2,X1] : (r2_hidden(X1,X2) | k3_enumset1(X1,X1,X1,X1,X1) = k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)) )),
% 1.26/0.52    inference(equality_resolution,[],[f63])).
% 1.26/0.52  fof(f63,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) | X0 != X1 | r2_hidden(X0,X2)) )),
% 1.26/0.52    inference(definition_unfolding,[],[f42,f60,f59])).
% 1.26/0.52  fof(f42,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | X0 != X1 | r2_hidden(X0,X2)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f25])).
% 1.26/0.52  fof(f25,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.26/0.52    inference(flattening,[],[f24])).
% 1.26/0.52  fof(f24,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.26/0.52    inference(nnf_transformation,[],[f13])).
% 1.26/0.52  fof(f13,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 1.26/0.52  fof(f124,plain,(
% 1.26/0.52    ( ! [X1] : (k1_xboole_0 != k3_enumset1(X1,X1,X1,X1,X1)) )),
% 1.26/0.52    inference(forward_demodulation,[],[f82,f85])).
% 1.26/0.52  fof(f85,plain,(
% 1.26/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.26/0.52    inference(forward_demodulation,[],[f73,f51])).
% 1.26/0.52  fof(f51,plain,(
% 1.26/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.26/0.52    inference(cnf_transformation,[],[f4])).
% 1.26/0.52  fof(f4,axiom,(
% 1.26/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.26/0.52  fof(f73,plain,(
% 1.26/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.26/0.52    inference(definition_unfolding,[],[f52,f55])).
% 1.26/0.52  fof(f55,plain,(
% 1.26/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f5])).
% 1.26/0.52  fof(f5,axiom,(
% 1.26/0.52    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.26/0.52  fof(f52,plain,(
% 1.26/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f3])).
% 1.26/0.52  fof(f3,axiom,(
% 1.26/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.26/0.52  fof(f82,plain,(
% 1.26/0.52    ( ! [X1] : (k3_enumset1(X1,X1,X1,X1,X1) != k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1))) )),
% 1.26/0.52    inference(equality_resolution,[],[f75])).
% 1.26/0.52  fof(f75,plain,(
% 1.26/0.52    ( ! [X0,X1] : (X0 != X1 | k3_enumset1(X0,X0,X0,X0,X0) != k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) )),
% 1.26/0.52    inference(definition_unfolding,[],[f53,f60,f60,f60])).
% 1.26/0.52  fof(f53,plain,(
% 1.26/0.52    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f31])).
% 1.26/0.52  fof(f31,plain,(
% 1.26/0.52    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.26/0.52    inference(nnf_transformation,[],[f15])).
% 1.26/0.52  fof(f15,axiom,(
% 1.26/0.52    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.26/0.52  fof(f34,plain,(
% 1.26/0.52    sK0 != sK3),
% 1.26/0.52    inference(cnf_transformation,[],[f22])).
% 1.26/0.52  fof(f33,plain,(
% 1.26/0.52    sK0 != sK2),
% 1.26/0.52    inference(cnf_transformation,[],[f22])).
% 1.26/0.52  % SZS output end Proof for theBenchmark
% 1.26/0.52  % (25021)------------------------------
% 1.26/0.52  % (25021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (25021)Termination reason: Refutation
% 1.26/0.52  
% 1.26/0.52  % (25021)Memory used [KB]: 1918
% 1.26/0.52  % (25021)Time elapsed: 0.090 s
% 1.26/0.52  % (25021)------------------------------
% 1.26/0.52  % (25021)------------------------------
% 1.26/0.52  % (25015)Success in time 0.162 s
%------------------------------------------------------------------------------

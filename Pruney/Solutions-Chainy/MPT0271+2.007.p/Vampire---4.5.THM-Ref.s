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
% DateTime   : Thu Dec  3 12:41:06 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 109 expanded)
%              Number of leaves         :   16 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  212 ( 402 expanded)
%              Number of equality atoms :   81 ( 153 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f490,plain,(
    $false ),
    inference(subsumption_resolution,[],[f488,f155])).

fof(f155,plain,(
    r2_hidden(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f150,f86])).

fof(f86,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f150,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_tarski(sK0))
      | r2_hidden(X1,sK1)
      | r2_hidden(sK0,sK1) ) ),
    inference(superposition,[],[f89,f145])).

fof(f145,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f139,f52])).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f139,plain,
    ( k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0)
    | r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f62,f48])).

fof(f48,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( r2_hidden(sK0,sK1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( r2_hidden(sK0,sK1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f488,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f435,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f435,plain,(
    ~ r1_tarski(k1_tarski(sK0),sK1) ),
    inference(subsumption_resolution,[],[f433,f155])).

fof(f433,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r1_tarski(k1_tarski(sK0),sK1) ),
    inference(trivial_inequality_removal,[],[f429])).

fof(f429,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK0,sK1)
    | ~ r1_tarski(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f49,f392])).

fof(f392,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f390,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f390,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,X1)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f61,f249])).

fof(f249,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = X1
      | ~ r1_tarski(X1,X2) ) ),
    inference(backward_demodulation,[],[f174,f235])).

fof(f235,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f203,f58])).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f203,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f182,f93])).

fof(f93,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f58,f53])).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f182,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f74,f50])).

fof(f74,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f174,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = k5_xboole_0(X2,k5_xboole_0(X1,X2))
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f164,f58])).

fof(f164,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f63,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:51:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (796131328)
% 0.14/0.36  ipcrm: permission denied for id (796164097)
% 0.14/0.37  ipcrm: permission denied for id (796196868)
% 0.14/0.37  ipcrm: permission denied for id (796229638)
% 0.14/0.37  ipcrm: permission denied for id (796295177)
% 0.14/0.38  ipcrm: permission denied for id (796360716)
% 0.14/0.38  ipcrm: permission denied for id (796426253)
% 0.14/0.38  ipcrm: permission denied for id (796491792)
% 0.14/0.39  ipcrm: permission denied for id (796557331)
% 0.14/0.39  ipcrm: permission denied for id (796622872)
% 0.14/0.40  ipcrm: permission denied for id (796688411)
% 0.21/0.40  ipcrm: permission denied for id (796753951)
% 0.21/0.42  ipcrm: permission denied for id (796950572)
% 0.21/0.42  ipcrm: permission denied for id (797016111)
% 0.21/0.42  ipcrm: permission denied for id (797048881)
% 0.21/0.43  ipcrm: permission denied for id (797114422)
% 0.21/0.45  ipcrm: permission denied for id (797311044)
% 0.21/0.45  ipcrm: permission denied for id (797343813)
% 0.21/0.46  ipcrm: permission denied for id (797442122)
% 0.21/0.47  ipcrm: permission denied for id (797573205)
% 0.21/0.47  ipcrm: permission denied for id (797605974)
% 0.21/0.48  ipcrm: permission denied for id (797704283)
% 0.21/0.49  ipcrm: permission denied for id (797769828)
% 0.21/0.49  ipcrm: permission denied for id (797835366)
% 0.21/0.49  ipcrm: permission denied for id (797868135)
% 0.21/0.50  ipcrm: permission denied for id (797900905)
% 0.21/0.50  ipcrm: permission denied for id (797933675)
% 0.21/0.50  ipcrm: permission denied for id (797966445)
% 0.21/0.51  ipcrm: permission denied for id (798031985)
% 0.21/0.51  ipcrm: permission denied for id (798064755)
% 0.21/0.52  ipcrm: permission denied for id (798130298)
% 0.21/0.52  ipcrm: permission denied for id (798163067)
% 0.21/0.52  ipcrm: permission denied for id (798195836)
% 0.21/0.52  ipcrm: permission denied for id (798294143)
% 1.08/0.65  % (13139)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.08/0.66  % (13156)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.08/0.68  % (13138)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.08/0.68  % (13164)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.08/0.68  % (13164)Refutation not found, incomplete strategy% (13164)------------------------------
% 1.08/0.68  % (13164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.68  % (13164)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.68  
% 1.08/0.68  % (13164)Memory used [KB]: 1663
% 1.08/0.68  % (13164)Time elapsed: 0.119 s
% 1.08/0.68  % (13164)------------------------------
% 1.08/0.68  % (13164)------------------------------
% 1.08/0.68  % (13137)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.08/0.68  % (13147)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.08/0.68  % (13155)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.08/0.68  % (13135)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.08/0.69  % (13146)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.08/0.69  % (13136)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.08/0.69  % (13158)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.08/0.70  % (13143)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.08/0.70  % (13161)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.08/0.70  % (13142)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.08/0.70  % (13145)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.08/0.70  % (13133)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.08/0.70  % (13151)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.08/0.70  % (13150)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.08/0.71  % (13153)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.08/0.71  % (13151)Refutation not found, incomplete strategy% (13151)------------------------------
% 1.08/0.71  % (13151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.71  % (13151)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.71  
% 1.08/0.71  % (13151)Memory used [KB]: 10618
% 1.08/0.71  % (13151)Time elapsed: 0.124 s
% 1.08/0.71  % (13151)------------------------------
% 1.08/0.71  % (13151)------------------------------
% 1.08/0.71  % (13148)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.08/0.71  % (13148)Refutation not found, incomplete strategy% (13148)------------------------------
% 1.08/0.71  % (13148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.71  % (13148)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.71  
% 1.08/0.71  % (13148)Memory used [KB]: 1663
% 1.08/0.71  % (13148)Time elapsed: 0.123 s
% 1.08/0.71  % (13148)------------------------------
% 1.08/0.71  % (13148)------------------------------
% 1.08/0.71  % (13159)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.08/0.71  % (13160)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.08/0.71  % (13140)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.08/0.71  % (13162)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.08/0.71  % (13162)Refutation not found, incomplete strategy% (13162)------------------------------
% 1.08/0.71  % (13162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.71  % (13162)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.71  
% 1.08/0.71  % (13162)Memory used [KB]: 6268
% 1.08/0.71  % (13162)Time elapsed: 0.138 s
% 1.08/0.71  % (13162)------------------------------
% 1.08/0.71  % (13162)------------------------------
% 1.08/0.71  % (13154)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.08/0.71  % (13152)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.08/0.72  % (13144)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.08/0.72  % (13163)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.08/0.72  % (13152)Refutation not found, incomplete strategy% (13152)------------------------------
% 1.08/0.72  % (13152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.72  % (13152)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.72  
% 1.08/0.72  % (13152)Memory used [KB]: 1791
% 1.08/0.72  % (13152)Time elapsed: 0.135 s
% 1.08/0.72  % (13152)------------------------------
% 1.08/0.72  % (13152)------------------------------
% 1.08/0.72  % (13157)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.08/0.72  % (13145)Refutation not found, incomplete strategy% (13145)------------------------------
% 1.08/0.72  % (13145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.72  % (13145)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.72  
% 1.08/0.72  % (13145)Memory used [KB]: 6268
% 1.08/0.72  % (13145)Time elapsed: 0.151 s
% 1.08/0.72  % (13145)------------------------------
% 1.08/0.72  % (13145)------------------------------
% 1.08/0.72  % (13141)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.08/0.72  % (13153)Refutation not found, incomplete strategy% (13153)------------------------------
% 1.08/0.72  % (13153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.72  % (13153)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.72  
% 1.08/0.72  % (13153)Memory used [KB]: 1663
% 1.08/0.72  % (13153)Time elapsed: 0.129 s
% 1.08/0.72  % (13153)------------------------------
% 1.08/0.72  % (13153)------------------------------
% 1.72/0.74  % (13143)Refutation found. Thanks to Tanya!
% 1.72/0.74  % SZS status Theorem for theBenchmark
% 1.72/0.74  % SZS output start Proof for theBenchmark
% 1.72/0.74  fof(f490,plain,(
% 1.72/0.74    $false),
% 1.72/0.74    inference(subsumption_resolution,[],[f488,f155])).
% 1.72/0.74  fof(f155,plain,(
% 1.72/0.74    r2_hidden(sK0,sK1)),
% 1.72/0.74    inference(duplicate_literal_removal,[],[f152])).
% 1.72/0.74  fof(f152,plain,(
% 1.72/0.74    r2_hidden(sK0,sK1) | r2_hidden(sK0,sK1)),
% 1.72/0.74    inference(resolution,[],[f150,f86])).
% 1.72/0.74  fof(f86,plain,(
% 1.72/0.74    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.72/0.74    inference(equality_resolution,[],[f85])).
% 1.72/0.74  fof(f85,plain,(
% 1.72/0.74    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.72/0.74    inference(equality_resolution,[],[f66])).
% 1.72/0.74  fof(f66,plain,(
% 1.72/0.74    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.72/0.74    inference(cnf_transformation,[],[f40])).
% 1.72/0.74  fof(f40,plain,(
% 1.72/0.74    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.72/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 1.72/0.74  fof(f39,plain,(
% 1.72/0.74    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.72/0.74    introduced(choice_axiom,[])).
% 1.72/0.74  fof(f38,plain,(
% 1.72/0.74    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.72/0.74    inference(rectify,[],[f37])).
% 1.72/0.74  fof(f37,plain,(
% 1.72/0.74    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.72/0.74    inference(nnf_transformation,[],[f14])).
% 1.72/0.74  fof(f14,axiom,(
% 1.72/0.74    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.72/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.72/0.74  fof(f150,plain,(
% 1.72/0.74    ( ! [X1] : (~r2_hidden(X1,k1_tarski(sK0)) | r2_hidden(X1,sK1) | r2_hidden(sK0,sK1)) )),
% 1.72/0.74    inference(superposition,[],[f89,f145])).
% 1.72/0.74  fof(f145,plain,(
% 1.72/0.74    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) | r2_hidden(sK0,sK1)),
% 1.72/0.74    inference(forward_demodulation,[],[f139,f52])).
% 1.72/0.74  fof(f52,plain,(
% 1.72/0.74    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.72/0.74    inference(cnf_transformation,[],[f7])).
% 1.72/0.74  fof(f7,axiom,(
% 1.72/0.74    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.72/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.72/0.74  fof(f139,plain,(
% 1.72/0.74    k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0) | r2_hidden(sK0,sK1)),
% 1.72/0.74    inference(superposition,[],[f62,f48])).
% 1.72/0.74  fof(f48,plain,(
% 1.72/0.74    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) | r2_hidden(sK0,sK1)),
% 1.72/0.74    inference(cnf_transformation,[],[f34])).
% 1.72/0.74  fof(f34,plain,(
% 1.72/0.74    (~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.72/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f33])).
% 1.72/0.74  fof(f33,plain,(
% 1.72/0.74    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))) => ((~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 1.72/0.74    introduced(choice_axiom,[])).
% 1.72/0.74  fof(f32,plain,(
% 1.72/0.74    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.72/0.74    inference(nnf_transformation,[],[f29])).
% 1.72/0.74  fof(f29,plain,(
% 1.72/0.74    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 1.72/0.74    inference(ennf_transformation,[],[f27])).
% 1.72/0.74  fof(f27,negated_conjecture,(
% 1.72/0.74    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.72/0.74    inference(negated_conjecture,[],[f26])).
% 1.72/0.74  fof(f26,conjecture,(
% 1.72/0.74    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.72/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 1.72/0.74  fof(f62,plain,(
% 1.72/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.72/0.74    inference(cnf_transformation,[],[f8])).
% 1.72/0.74  fof(f8,axiom,(
% 1.72/0.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.72/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.72/0.74  fof(f89,plain,(
% 1.72/0.74    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.72/0.74    inference(equality_resolution,[],[f77])).
% 1.72/0.74  fof(f77,plain,(
% 1.72/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 1.72/0.74    inference(cnf_transformation,[],[f47])).
% 1.72/0.74  fof(f47,plain,(
% 1.72/0.74    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.72/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).
% 1.72/0.74  fof(f46,plain,(
% 1.72/0.74    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.72/0.74    introduced(choice_axiom,[])).
% 1.72/0.74  fof(f45,plain,(
% 1.72/0.74    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.72/0.74    inference(rectify,[],[f44])).
% 1.72/0.74  fof(f44,plain,(
% 1.72/0.74    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.72/0.74    inference(flattening,[],[f43])).
% 1.72/0.74  fof(f43,plain,(
% 1.72/0.74    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.72/0.74    inference(nnf_transformation,[],[f2])).
% 1.72/0.74  fof(f2,axiom,(
% 1.72/0.74    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.72/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.72/0.74  fof(f488,plain,(
% 1.72/0.74    ~r2_hidden(sK0,sK1)),
% 1.72/0.74    inference(resolution,[],[f435,f70])).
% 1.72/0.74  fof(f70,plain,(
% 1.72/0.74    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.72/0.74    inference(cnf_transformation,[],[f41])).
% 1.72/0.74  fof(f41,plain,(
% 1.72/0.74    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.72/0.74    inference(nnf_transformation,[],[f22])).
% 1.72/0.74  fof(f22,axiom,(
% 1.72/0.74    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.72/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.72/0.74  fof(f435,plain,(
% 1.72/0.74    ~r1_tarski(k1_tarski(sK0),sK1)),
% 1.72/0.74    inference(subsumption_resolution,[],[f433,f155])).
% 1.72/0.74  fof(f433,plain,(
% 1.72/0.74    ~r2_hidden(sK0,sK1) | ~r1_tarski(k1_tarski(sK0),sK1)),
% 1.72/0.74    inference(trivial_inequality_removal,[],[f429])).
% 1.72/0.74  fof(f429,plain,(
% 1.72/0.74    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK0,sK1) | ~r1_tarski(k1_tarski(sK0),sK1)),
% 1.72/0.74    inference(superposition,[],[f49,f392])).
% 1.72/0.74  fof(f392,plain,(
% 1.72/0.74    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,X2) | ~r1_tarski(X1,X2)) )),
% 1.72/0.74    inference(forward_demodulation,[],[f390,f50])).
% 1.72/0.74  fof(f50,plain,(
% 1.72/0.74    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.72/0.74    inference(cnf_transformation,[],[f11])).
% 1.72/0.74  fof(f11,axiom,(
% 1.72/0.74    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.72/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.72/0.74  fof(f390,plain,(
% 1.72/0.74    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,X1) | ~r1_tarski(X1,X2)) )),
% 1.72/0.74    inference(superposition,[],[f61,f249])).
% 1.72/0.74  fof(f249,plain,(
% 1.72/0.74    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = X1 | ~r1_tarski(X1,X2)) )),
% 1.72/0.74    inference(backward_demodulation,[],[f174,f235])).
% 1.72/0.74  fof(f235,plain,(
% 1.72/0.74    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.72/0.74    inference(superposition,[],[f203,f58])).
% 1.72/0.74  fof(f58,plain,(
% 1.72/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.72/0.74    inference(cnf_transformation,[],[f1])).
% 1.72/0.74  fof(f1,axiom,(
% 1.72/0.74    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.72/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.72/0.74  fof(f203,plain,(
% 1.72/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.72/0.74    inference(forward_demodulation,[],[f182,f93])).
% 1.72/0.74  fof(f93,plain,(
% 1.72/0.74    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.72/0.74    inference(superposition,[],[f58,f53])).
% 1.72/0.74  fof(f53,plain,(
% 1.72/0.74    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.72/0.74    inference(cnf_transformation,[],[f9])).
% 1.72/0.74  fof(f9,axiom,(
% 1.72/0.74    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.72/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.72/0.74  fof(f182,plain,(
% 1.72/0.74    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.72/0.74    inference(superposition,[],[f74,f50])).
% 1.72/0.74  fof(f74,plain,(
% 1.72/0.74    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.72/0.74    inference(cnf_transformation,[],[f10])).
% 1.72/0.74  fof(f10,axiom,(
% 1.72/0.74    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.72/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.72/0.74  fof(f174,plain,(
% 1.72/0.74    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) | ~r1_tarski(X1,X2)) )),
% 1.72/0.74    inference(forward_demodulation,[],[f164,f58])).
% 1.72/0.74  fof(f164,plain,(
% 1.72/0.74    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),X2) | ~r1_tarski(X1,X2)) )),
% 1.72/0.74    inference(superposition,[],[f63,f64])).
% 1.72/0.74  fof(f64,plain,(
% 1.72/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.72/0.74    inference(cnf_transformation,[],[f31])).
% 1.72/0.74  fof(f31,plain,(
% 1.72/0.74    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.72/0.74    inference(ennf_transformation,[],[f6])).
% 1.72/0.74  fof(f6,axiom,(
% 1.72/0.74    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.72/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.72/0.74  fof(f63,plain,(
% 1.72/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.72/0.74    inference(cnf_transformation,[],[f12])).
% 1.72/0.74  fof(f12,axiom,(
% 1.72/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.72/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.72/0.74  fof(f61,plain,(
% 1.72/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.72/0.74    inference(cnf_transformation,[],[f5])).
% 1.72/0.74  fof(f5,axiom,(
% 1.72/0.74    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.72/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.72/0.74  fof(f49,plain,(
% 1.72/0.74    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 1.72/0.74    inference(cnf_transformation,[],[f34])).
% 1.72/0.74  % SZS output end Proof for theBenchmark
% 1.72/0.74  % (13143)------------------------------
% 1.72/0.74  % (13143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.74  % (13143)Termination reason: Refutation
% 1.72/0.74  
% 1.72/0.74  % (13143)Memory used [KB]: 2046
% 1.72/0.74  % (13143)Time elapsed: 0.170 s
% 1.72/0.74  % (13143)------------------------------
% 1.72/0.74  % (13143)------------------------------
% 1.72/0.75  % (12950)Success in time 0.384 s
%------------------------------------------------------------------------------

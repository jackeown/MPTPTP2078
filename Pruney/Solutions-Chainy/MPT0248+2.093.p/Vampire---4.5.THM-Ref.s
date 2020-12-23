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
% DateTime   : Thu Dec  3 12:38:03 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  111 (1268 expanded)
%              Number of leaves         :   19 ( 342 expanded)
%              Depth                    :   26
%              Number of atoms          :  285 (5480 expanded)
%              Number of equality atoms :  155 (3090 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f796,plain,(
    $false ),
    inference(subsumption_resolution,[],[f795,f349])).

fof(f349,plain,(
    sK1 != sK2 ),
    inference(subsumption_resolution,[],[f95,f348])).

fof(f348,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(global_subsumption,[],[f52,f230,f340])).

fof(f340,plain,
    ( sK2 = k1_tarski(sK0)
    | sK1 = k1_tarski(sK0) ),
    inference(superposition,[],[f306,f50])).

fof(f50,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f306,plain,(
    ! [X0] :
      ( k2_xboole_0(sK1,X0) = X0
      | sK1 = k1_tarski(sK0) ) ),
    inference(resolution,[],[f294,f229])).

fof(f229,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f227,f137])).

fof(f137,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f68,f98])).

fof(f98,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f59,f50])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f227,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r1_tarski(k1_tarski(sK0),sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(superposition,[],[f71,f188])).

fof(f188,plain,
    ( sK0 = sK4(k1_tarski(sK0),sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f109,f137])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | sK4(k1_tarski(X0),X1) = X0 ) ),
    inference(resolution,[],[f70,f93])).

fof(f93,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f294,plain,(
    ! [X1] :
      ( r2_hidden(sK0,sK1)
      | k2_xboole_0(sK1,X1) = X1 ) ),
    inference(subsumption_resolution,[],[f291,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f291,plain,(
    ! [X1] :
      ( r2_hidden(sK0,sK1)
      | r1_tarski(sK1,X1)
      | k2_xboole_0(sK1,X1) = X1 ) ),
    inference(superposition,[],[f70,f169])).

fof(f169,plain,(
    ! [X3] :
      ( sK0 = sK4(sK1,X3)
      | k2_xboole_0(sK1,X3) = X3 ) ),
    inference(resolution,[],[f153,f65])).

fof(f153,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | sK0 = sK4(sK1,X0) ) ),
    inference(resolution,[],[f150,f70])).

fof(f150,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK0 = X0 ) ),
    inference(resolution,[],[f147,f93])).

fof(f147,plain,(
    ! [X10] :
      ( r2_hidden(X10,k1_tarski(sK0))
      | ~ r2_hidden(X10,sK1) ) ),
    inference(resolution,[],[f69,f98])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f230,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f229,f155])).

fof(f155,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f56,f152])).

fof(f152,plain,
    ( sK0 = sK3(sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f150,f56])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f52,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f34])).

fof(f95,plain,
    ( sK1 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(inner_rewriting,[],[f94])).

fof(f94,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f51])).

fof(f51,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f795,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f792,f351])).

fof(f351,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f50,f348])).

fof(f792,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f791,f293])).

fof(f293,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | k2_xboole_0(sK1,X0) = X0 ) ),
    inference(subsumption_resolution,[],[f290,f65])).

fof(f290,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | r1_tarski(sK1,X0)
      | k2_xboole_0(sK1,X0) = X0 ) ),
    inference(superposition,[],[f71,f169])).

fof(f791,plain,(
    r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f790,f350])).

fof(f350,plain,(
    k1_xboole_0 != sK2 ),
    inference(subsumption_resolution,[],[f53,f348])).

fof(f53,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f790,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f56,f785])).

fof(f785,plain,(
    sK0 = sK3(sK2) ),
    inference(resolution,[],[f784,f150])).

fof(f784,plain,(
    r2_hidden(sK3(sK2),sK1) ),
    inference(subsumption_resolution,[],[f782,f350])).

fof(f782,plain,
    ( r2_hidden(sK3(sK2),sK1)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f762,f56])).

fof(f762,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,sK2)
      | r2_hidden(X12,sK1) ) ),
    inference(superposition,[],[f749,f494])).

fof(f494,plain,(
    sK2 = k3_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f432,f492])).

fof(f492,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f479,f443])).

fof(f443,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f440,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f440,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f425,f242])).

fof(f242,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f241,f57])).

fof(f57,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f241,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f232,f58])).

fof(f58,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f232,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f64,f54])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f425,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f77,f54])).

fof(f77,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f479,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f440,f433])).

fof(f433,plain,(
    ! [X6,X5] : k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6))) ),
    inference(superposition,[],[f77,f54])).

fof(f432,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f77,f358])).

fof(f358,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) ),
    inference(backward_demodulation,[],[f239,f348])).

fof(f239,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0)) ),
    inference(superposition,[],[f64,f50])).

fof(f749,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X7,k3_xboole_0(X5,X6))
      | r2_hidden(X7,X5) ) ),
    inference(subsumption_resolution,[],[f733,f146])).

fof(f146,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X7,k4_xboole_0(X8,X9))
      | r2_hidden(X7,X8) ) ),
    inference(resolution,[],[f69,f60])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f733,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X7,k3_xboole_0(X5,X6))
      | r2_hidden(X7,X5)
      | r2_hidden(X7,k4_xboole_0(X5,X6)) ) ),
    inference(superposition,[],[f78,f444])).

fof(f444,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f440,f63])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:33:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (30976)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (30967)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (30965)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (30984)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (30992)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (30990)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (30963)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (30983)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (30973)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (30978)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (30973)Refutation not found, incomplete strategy% (30973)------------------------------
% 0.21/0.53  % (30973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30973)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30973)Memory used [KB]: 10618
% 0.21/0.53  % (30973)Time elapsed: 0.118 s
% 0.21/0.53  % (30973)------------------------------
% 0.21/0.53  % (30973)------------------------------
% 0.21/0.53  % (30982)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (30975)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (30970)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (30964)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (30977)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (30966)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (30972)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (30974)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (30989)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (30981)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (30988)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (30968)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (30991)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (30979)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (30974)Refutation not found, incomplete strategy% (30974)------------------------------
% 0.21/0.54  % (30974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30971)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (30969)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (30980)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (30987)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (30985)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (30986)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (30974)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (30974)Memory used [KB]: 10874
% 0.21/0.56  % (30974)Time elapsed: 0.131 s
% 0.21/0.56  % (30974)------------------------------
% 0.21/0.56  % (30974)------------------------------
% 1.80/0.59  % (30970)Refutation found. Thanks to Tanya!
% 1.80/0.59  % SZS status Theorem for theBenchmark
% 1.80/0.59  % SZS output start Proof for theBenchmark
% 1.80/0.59  fof(f796,plain,(
% 1.80/0.59    $false),
% 1.80/0.59    inference(subsumption_resolution,[],[f795,f349])).
% 1.80/0.59  fof(f349,plain,(
% 1.80/0.59    sK1 != sK2),
% 1.80/0.59    inference(subsumption_resolution,[],[f95,f348])).
% 1.80/0.59  fof(f348,plain,(
% 1.80/0.59    sK1 = k1_tarski(sK0)),
% 1.80/0.59    inference(global_subsumption,[],[f52,f230,f340])).
% 1.80/0.59  fof(f340,plain,(
% 1.80/0.59    sK2 = k1_tarski(sK0) | sK1 = k1_tarski(sK0)),
% 1.80/0.59    inference(superposition,[],[f306,f50])).
% 1.80/0.59  fof(f50,plain,(
% 1.80/0.59    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.80/0.59    inference(cnf_transformation,[],[f34])).
% 1.80/0.59  fof(f34,plain,(
% 1.80/0.59    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.80/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f33])).
% 1.80/0.59  fof(f33,plain,(
% 1.80/0.59    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.80/0.59    introduced(choice_axiom,[])).
% 1.80/0.59  fof(f28,plain,(
% 1.80/0.59    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.80/0.59    inference(ennf_transformation,[],[f25])).
% 1.80/0.59  fof(f25,negated_conjecture,(
% 1.80/0.59    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.80/0.59    inference(negated_conjecture,[],[f24])).
% 1.80/0.59  fof(f24,conjecture,(
% 1.80/0.59    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.80/0.59  fof(f306,plain,(
% 1.80/0.59    ( ! [X0] : (k2_xboole_0(sK1,X0) = X0 | sK1 = k1_tarski(sK0)) )),
% 1.80/0.59    inference(resolution,[],[f294,f229])).
% 1.80/0.59  fof(f229,plain,(
% 1.80/0.59    ~r2_hidden(sK0,sK1) | sK1 = k1_tarski(sK0)),
% 1.80/0.59    inference(subsumption_resolution,[],[f227,f137])).
% 1.80/0.59  fof(f137,plain,(
% 1.80/0.59    ~r1_tarski(k1_tarski(sK0),sK1) | sK1 = k1_tarski(sK0)),
% 1.80/0.59    inference(resolution,[],[f68,f98])).
% 1.80/0.59  fof(f98,plain,(
% 1.80/0.59    r1_tarski(sK1,k1_tarski(sK0))),
% 1.80/0.59    inference(superposition,[],[f59,f50])).
% 1.80/0.59  fof(f59,plain,(
% 1.80/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.80/0.59    inference(cnf_transformation,[],[f10])).
% 1.80/0.59  fof(f10,axiom,(
% 1.80/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.80/0.59  fof(f68,plain,(
% 1.80/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.80/0.59    inference(cnf_transformation,[],[f38])).
% 1.80/0.59  fof(f38,plain,(
% 1.80/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.80/0.59    inference(flattening,[],[f37])).
% 1.80/0.59  fof(f37,plain,(
% 1.80/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.80/0.59    inference(nnf_transformation,[],[f6])).
% 1.80/0.59  fof(f6,axiom,(
% 1.80/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.80/0.59  fof(f227,plain,(
% 1.80/0.59    ~r2_hidden(sK0,sK1) | r1_tarski(k1_tarski(sK0),sK1) | sK1 = k1_tarski(sK0)),
% 1.80/0.59    inference(superposition,[],[f71,f188])).
% 1.80/0.59  fof(f188,plain,(
% 1.80/0.59    sK0 = sK4(k1_tarski(sK0),sK1) | sK1 = k1_tarski(sK0)),
% 1.80/0.59    inference(resolution,[],[f109,f137])).
% 1.80/0.59  fof(f109,plain,(
% 1.80/0.59    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | sK4(k1_tarski(X0),X1) = X0) )),
% 1.80/0.59    inference(resolution,[],[f70,f93])).
% 1.80/0.59  fof(f93,plain,(
% 1.80/0.59    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.80/0.59    inference(equality_resolution,[],[f72])).
% 1.80/0.59  fof(f72,plain,(
% 1.80/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.80/0.59    inference(cnf_transformation,[],[f46])).
% 1.80/0.59  fof(f46,plain,(
% 1.80/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.80/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).
% 1.80/0.59  fof(f45,plain,(
% 1.80/0.59    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.80/0.59    introduced(choice_axiom,[])).
% 1.80/0.59  fof(f44,plain,(
% 1.80/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.80/0.59    inference(rectify,[],[f43])).
% 1.80/0.59  fof(f43,plain,(
% 1.80/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.80/0.59    inference(nnf_transformation,[],[f14])).
% 1.80/0.59  fof(f14,axiom,(
% 1.80/0.59    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.80/0.59  fof(f70,plain,(
% 1.80/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f42])).
% 1.80/0.59  fof(f42,plain,(
% 1.80/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.80/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 1.80/0.59  fof(f41,plain,(
% 1.80/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.80/0.59    introduced(choice_axiom,[])).
% 1.80/0.59  fof(f40,plain,(
% 1.80/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.80/0.59    inference(rectify,[],[f39])).
% 1.80/0.59  fof(f39,plain,(
% 1.80/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.80/0.59    inference(nnf_transformation,[],[f31])).
% 1.80/0.59  fof(f31,plain,(
% 1.80/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.80/0.59    inference(ennf_transformation,[],[f1])).
% 1.80/0.59  fof(f1,axiom,(
% 1.80/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.80/0.59  fof(f71,plain,(
% 1.80/0.59    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f42])).
% 1.80/0.59  fof(f294,plain,(
% 1.80/0.59    ( ! [X1] : (r2_hidden(sK0,sK1) | k2_xboole_0(sK1,X1) = X1) )),
% 1.80/0.59    inference(subsumption_resolution,[],[f291,f65])).
% 1.80/0.59  fof(f65,plain,(
% 1.80/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.80/0.59    inference(cnf_transformation,[],[f30])).
% 1.80/0.59  fof(f30,plain,(
% 1.80/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.80/0.59    inference(ennf_transformation,[],[f8])).
% 1.80/0.59  fof(f8,axiom,(
% 1.80/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.80/0.59  fof(f291,plain,(
% 1.80/0.59    ( ! [X1] : (r2_hidden(sK0,sK1) | r1_tarski(sK1,X1) | k2_xboole_0(sK1,X1) = X1) )),
% 1.80/0.59    inference(superposition,[],[f70,f169])).
% 1.80/0.59  fof(f169,plain,(
% 1.80/0.59    ( ! [X3] : (sK0 = sK4(sK1,X3) | k2_xboole_0(sK1,X3) = X3) )),
% 1.80/0.59    inference(resolution,[],[f153,f65])).
% 1.80/0.59  fof(f153,plain,(
% 1.80/0.59    ( ! [X0] : (r1_tarski(sK1,X0) | sK0 = sK4(sK1,X0)) )),
% 1.80/0.59    inference(resolution,[],[f150,f70])).
% 1.80/0.59  fof(f150,plain,(
% 1.80/0.59    ( ! [X0] : (~r2_hidden(X0,sK1) | sK0 = X0) )),
% 1.80/0.59    inference(resolution,[],[f147,f93])).
% 1.80/0.59  fof(f147,plain,(
% 1.80/0.59    ( ! [X10] : (r2_hidden(X10,k1_tarski(sK0)) | ~r2_hidden(X10,sK1)) )),
% 1.80/0.59    inference(resolution,[],[f69,f98])).
% 1.80/0.59  fof(f69,plain,(
% 1.80/0.59    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f42])).
% 1.80/0.59  fof(f230,plain,(
% 1.80/0.59    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 1.80/0.59    inference(resolution,[],[f229,f155])).
% 1.80/0.59  fof(f155,plain,(
% 1.80/0.59    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1),
% 1.80/0.59    inference(duplicate_literal_removal,[],[f154])).
% 1.80/0.59  fof(f154,plain,(
% 1.80/0.59    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.80/0.59    inference(superposition,[],[f56,f152])).
% 1.80/0.59  fof(f152,plain,(
% 1.80/0.59    sK0 = sK3(sK1) | k1_xboole_0 = sK1),
% 1.80/0.59    inference(resolution,[],[f150,f56])).
% 1.80/0.59  fof(f56,plain,(
% 1.80/0.59    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.80/0.59    inference(cnf_transformation,[],[f36])).
% 1.80/0.59  fof(f36,plain,(
% 1.80/0.59    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.80/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f35])).
% 1.80/0.59  fof(f35,plain,(
% 1.80/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.80/0.59    introduced(choice_axiom,[])).
% 1.80/0.59  fof(f29,plain,(
% 1.80/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.80/0.59    inference(ennf_transformation,[],[f5])).
% 1.80/0.59  fof(f5,axiom,(
% 1.80/0.59    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.80/0.59  fof(f52,plain,(
% 1.80/0.59    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.80/0.59    inference(cnf_transformation,[],[f34])).
% 1.80/0.59  fof(f95,plain,(
% 1.80/0.59    sK1 != sK2 | sK1 != k1_tarski(sK0)),
% 1.80/0.59    inference(inner_rewriting,[],[f94])).
% 1.80/0.59  fof(f94,plain,(
% 1.80/0.59    sK2 != k1_tarski(sK0) | sK1 != sK2),
% 1.80/0.59    inference(inner_rewriting,[],[f51])).
% 1.80/0.59  fof(f51,plain,(
% 1.80/0.59    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.80/0.59    inference(cnf_transformation,[],[f34])).
% 1.80/0.59  fof(f795,plain,(
% 1.80/0.59    sK1 = sK2),
% 1.80/0.59    inference(forward_demodulation,[],[f792,f351])).
% 1.80/0.59  fof(f351,plain,(
% 1.80/0.59    sK1 = k2_xboole_0(sK1,sK2)),
% 1.80/0.59    inference(backward_demodulation,[],[f50,f348])).
% 1.80/0.59  fof(f792,plain,(
% 1.80/0.59    sK2 = k2_xboole_0(sK1,sK2)),
% 1.80/0.59    inference(resolution,[],[f791,f293])).
% 1.80/0.59  fof(f293,plain,(
% 1.80/0.59    ( ! [X0] : (~r2_hidden(sK0,X0) | k2_xboole_0(sK1,X0) = X0) )),
% 1.80/0.59    inference(subsumption_resolution,[],[f290,f65])).
% 1.80/0.59  fof(f290,plain,(
% 1.80/0.59    ( ! [X0] : (~r2_hidden(sK0,X0) | r1_tarski(sK1,X0) | k2_xboole_0(sK1,X0) = X0) )),
% 1.80/0.59    inference(superposition,[],[f71,f169])).
% 1.80/0.59  fof(f791,plain,(
% 1.80/0.59    r2_hidden(sK0,sK2)),
% 1.80/0.59    inference(subsumption_resolution,[],[f790,f350])).
% 1.80/0.59  fof(f350,plain,(
% 1.80/0.59    k1_xboole_0 != sK2),
% 1.80/0.59    inference(subsumption_resolution,[],[f53,f348])).
% 1.80/0.59  fof(f53,plain,(
% 1.80/0.59    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.80/0.59    inference(cnf_transformation,[],[f34])).
% 1.80/0.59  fof(f790,plain,(
% 1.80/0.59    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2),
% 1.80/0.59    inference(superposition,[],[f56,f785])).
% 1.80/0.59  fof(f785,plain,(
% 1.80/0.59    sK0 = sK3(sK2)),
% 1.80/0.59    inference(resolution,[],[f784,f150])).
% 1.80/0.59  fof(f784,plain,(
% 1.80/0.59    r2_hidden(sK3(sK2),sK1)),
% 1.80/0.59    inference(subsumption_resolution,[],[f782,f350])).
% 1.80/0.59  fof(f782,plain,(
% 1.80/0.59    r2_hidden(sK3(sK2),sK1) | k1_xboole_0 = sK2),
% 1.80/0.59    inference(resolution,[],[f762,f56])).
% 1.80/0.59  fof(f762,plain,(
% 1.80/0.59    ( ! [X12] : (~r2_hidden(X12,sK2) | r2_hidden(X12,sK1)) )),
% 1.80/0.59    inference(superposition,[],[f749,f494])).
% 1.80/0.59  fof(f494,plain,(
% 1.80/0.59    sK2 = k3_xboole_0(sK1,sK2)),
% 1.80/0.59    inference(backward_demodulation,[],[f432,f492])).
% 1.80/0.59  fof(f492,plain,(
% 1.80/0.59    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 1.80/0.59    inference(forward_demodulation,[],[f479,f443])).
% 1.80/0.59  fof(f443,plain,(
% 1.80/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.80/0.59    inference(superposition,[],[f440,f54])).
% 1.80/0.59  fof(f54,plain,(
% 1.80/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f12])).
% 1.80/0.59  fof(f12,axiom,(
% 1.80/0.59    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.80/0.59  fof(f440,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.80/0.59    inference(forward_demodulation,[],[f425,f242])).
% 1.80/0.59  fof(f242,plain,(
% 1.80/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.80/0.59    inference(forward_demodulation,[],[f241,f57])).
% 1.80/0.59  fof(f57,plain,(
% 1.80/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.80/0.59    inference(cnf_transformation,[],[f26])).
% 1.80/0.59  fof(f26,plain,(
% 1.80/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.80/0.59    inference(rectify,[],[f3])).
% 1.80/0.59  fof(f3,axiom,(
% 1.80/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.80/0.59  fof(f241,plain,(
% 1.80/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.80/0.59    inference(forward_demodulation,[],[f232,f58])).
% 1.80/0.59  fof(f58,plain,(
% 1.80/0.59    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.80/0.59    inference(cnf_transformation,[],[f27])).
% 1.80/0.59  fof(f27,plain,(
% 1.80/0.59    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.80/0.59    inference(rectify,[],[f2])).
% 1.80/0.59  fof(f2,axiom,(
% 1.80/0.59    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.80/0.59  fof(f232,plain,(
% 1.80/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 1.80/0.59    inference(superposition,[],[f64,f54])).
% 1.80/0.59  fof(f64,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.80/0.59    inference(cnf_transformation,[],[f13])).
% 1.80/0.59  fof(f13,axiom,(
% 1.80/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.80/0.59  fof(f425,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.80/0.59    inference(superposition,[],[f77,f54])).
% 1.80/0.59  fof(f77,plain,(
% 1.80/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.80/0.59    inference(cnf_transformation,[],[f11])).
% 1.80/0.59  fof(f11,axiom,(
% 1.80/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.80/0.59  fof(f479,plain,(
% 1.80/0.59    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 1.80/0.59    inference(superposition,[],[f440,f433])).
% 1.80/0.59  fof(f433,plain,(
% 1.80/0.59    ( ! [X6,X5] : (k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6)))) )),
% 1.80/0.59    inference(superposition,[],[f77,f54])).
% 1.80/0.59  fof(f432,plain,(
% 1.80/0.59    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),
% 1.80/0.59    inference(superposition,[],[f77,f358])).
% 1.80/0.59  fof(f358,plain,(
% 1.80/0.59    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)),
% 1.80/0.59    inference(backward_demodulation,[],[f239,f348])).
% 1.80/0.59  fof(f239,plain,(
% 1.80/0.59    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0))),
% 1.80/0.59    inference(superposition,[],[f64,f50])).
% 1.80/0.59  fof(f749,plain,(
% 1.80/0.59    ( ! [X6,X7,X5] : (~r2_hidden(X7,k3_xboole_0(X5,X6)) | r2_hidden(X7,X5)) )),
% 1.80/0.59    inference(subsumption_resolution,[],[f733,f146])).
% 1.80/0.59  fof(f146,plain,(
% 1.80/0.59    ( ! [X8,X7,X9] : (~r2_hidden(X7,k4_xboole_0(X8,X9)) | r2_hidden(X7,X8)) )),
% 1.80/0.59    inference(resolution,[],[f69,f60])).
% 1.80/0.59  fof(f60,plain,(
% 1.80/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f9])).
% 1.80/0.59  fof(f9,axiom,(
% 1.80/0.59    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.80/0.59  fof(f733,plain,(
% 1.80/0.59    ( ! [X6,X7,X5] : (~r2_hidden(X7,k3_xboole_0(X5,X6)) | r2_hidden(X7,X5) | r2_hidden(X7,k4_xboole_0(X5,X6))) )),
% 1.80/0.59    inference(superposition,[],[f78,f444])).
% 1.80/0.59  fof(f444,plain,(
% 1.80/0.59    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 1.80/0.59    inference(superposition,[],[f440,f63])).
% 1.80/0.59  fof(f63,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.80/0.59    inference(cnf_transformation,[],[f7])).
% 1.80/0.59  fof(f7,axiom,(
% 1.80/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.80/0.59  fof(f78,plain,(
% 1.80/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f47])).
% 1.80/0.59  fof(f47,plain,(
% 1.80/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.80/0.59    inference(nnf_transformation,[],[f32])).
% 1.80/0.59  fof(f32,plain,(
% 1.80/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.80/0.59    inference(ennf_transformation,[],[f4])).
% 1.80/0.59  fof(f4,axiom,(
% 1.80/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.80/0.59  % SZS output end Proof for theBenchmark
% 1.80/0.59  % (30970)------------------------------
% 1.80/0.59  % (30970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.59  % (30970)Termination reason: Refutation
% 1.80/0.59  
% 1.80/0.59  % (30970)Memory used [KB]: 6908
% 1.80/0.59  % (30970)Time elapsed: 0.158 s
% 1.80/0.59  % (30970)------------------------------
% 1.80/0.59  % (30970)------------------------------
% 1.80/0.60  % (30962)Success in time 0.234 s
%------------------------------------------------------------------------------

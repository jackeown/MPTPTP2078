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
% DateTime   : Thu Dec  3 12:39:06 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 229 expanded)
%              Number of leaves         :   18 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  275 ( 678 expanded)
%              Number of equality atoms :   57 ( 158 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f501,plain,(
    $false ),
    inference(subsumption_resolution,[],[f500,f133])).

fof(f133,plain,(
    sK3 != k2_xboole_0(sK3,k2_tarski(sK2,sK4)) ),
    inference(superposition,[],[f57,f128])).

fof(f128,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f102,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f102,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f61,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f57,plain,(
    sK3 != k2_xboole_0(k2_tarski(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( sK3 != k2_xboole_0(k2_tarski(sK2,sK4),sK3)
    & r2_hidden(sK4,sK3)
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( sK3 != k2_xboole_0(k2_tarski(sK2,sK4),sK3)
      & r2_hidden(sK4,sK3)
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f500,plain,(
    sK3 = k2_xboole_0(sK3,k2_tarski(sK2,sK4)) ),
    inference(forward_demodulation,[],[f490,f59])).

fof(f59,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f490,plain,(
    k2_xboole_0(sK3,k2_tarski(sK2,sK4)) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f64,f439])).

fof(f439,plain,(
    k1_xboole_0 = k4_xboole_0(k2_tarski(sK2,sK4),sK3) ),
    inference(backward_demodulation,[],[f275,f435])).

fof(f435,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f141,f424])).

fof(f424,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(X7,X7) ),
    inference(resolution,[],[f420,f317])).

fof(f317,plain,(
    ! [X17] :
      ( r2_hidden(sK6(X17,k1_xboole_0),X17)
      | k1_xboole_0 = X17 ) ),
    inference(resolution,[],[f70,f208])).

fof(f208,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f205])).

fof(f205,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f77,f181])).

fof(f181,plain,(
    ! [X3] : sP0(X3,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f154,f174])).

fof(f174,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f172,f142])).

fof(f142,plain,(
    ! [X0,X1] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f140,f140])).

fof(f140,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f63,f106])).

fof(f106,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f68,f58])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f172,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(forward_demodulation,[],[f166,f130])).

fof(f130,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f128,f59])).

fof(f166,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f64,f130])).

fof(f154,plain,(
    ! [X2,X3] : sP0(X3,k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f144,f142])).

fof(f144,plain,(
    ! [X0] : sP0(X0,k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f143,f141])).

fof(f143,plain,(
    ! [X0] : sP0(X0,k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f98,f140])).

fof(f98,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f4,f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
              & r2_hidden(sK7(X0,X1,X2),X1) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
            & r2_hidden(sK7(X0,X1,X2),X1) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | r2_hidden(sK6(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK6(X0,X1),X1)
          | ~ r2_hidden(sK6(X0,X1),X0) )
        & ( r2_hidden(sK6(X0,X1),X1)
          | r2_hidden(sK6(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1),X1)
          | ~ r2_hidden(sK6(X0,X1),X0) )
        & ( r2_hidden(sK6(X0,X1),X1)
          | r2_hidden(sK6(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f420,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,X1)) ),
    inference(condensation,[],[f417])).

fof(f417,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X2,X2)) ) ),
    inference(resolution,[],[f413,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f413,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(duplicate_literal_removal,[],[f406])).

fof(f406,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k4_xboole_0(X0,X0),X1)
      | r1_xboole_0(k4_xboole_0(X0,X0),X1) ) ),
    inference(resolution,[],[f215,f200])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(k4_xboole_0(X0,X1),X2),X0)
      | r1_xboole_0(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f197,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f76,f98])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f215,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(k4_xboole_0(X0,X1),X2),X1)
      | r1_xboole_0(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f204,f65])).

fof(f204,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f77,f98])).

fof(f141,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f63,f107])).

fof(f107,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(resolution,[],[f68,f96])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f275,plain,(
    k4_xboole_0(k2_tarski(sK2,sK4),sK3) = k5_xboole_0(k2_tarski(sK2,sK4),k2_tarski(sK2,sK4)) ),
    inference(superposition,[],[f63,f252])).

fof(f252,plain,(
    k2_tarski(sK2,sK4) = k3_xboole_0(k2_tarski(sK2,sK4),sK3) ),
    inference(resolution,[],[f242,f68])).

fof(f242,plain,(
    r1_tarski(k2_tarski(sK2,sK4),sK3) ),
    inference(resolution,[],[f239,f56])).

fof(f56,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f239,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,sK3)
      | r1_tarski(k2_tarski(sK2,X12),sK3) ) ),
    inference(resolution,[],[f94,f55])).

fof(f55,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n013.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 13:53:54 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.49  % (26807)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.18/0.49  % (26806)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.18/0.49  % (26819)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.18/0.50  % (26825)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.18/0.50  % (26815)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.18/0.50  % (26814)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.18/0.50  % (26815)Refutation not found, incomplete strategy% (26815)------------------------------
% 0.18/0.50  % (26815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.50  % (26814)Refutation not found, incomplete strategy% (26814)------------------------------
% 0.18/0.50  % (26814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.50  % (26815)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.50  
% 0.18/0.50  % (26815)Memory used [KB]: 10618
% 0.18/0.50  % (26815)Time elapsed: 0.107 s
% 0.18/0.50  % (26815)------------------------------
% 0.18/0.50  % (26815)------------------------------
% 0.18/0.50  % (26821)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.18/0.50  % (26814)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.50  
% 0.18/0.50  % (26814)Memory used [KB]: 10618
% 0.18/0.50  % (26814)Time elapsed: 0.114 s
% 0.18/0.50  % (26814)------------------------------
% 0.18/0.50  % (26814)------------------------------
% 0.18/0.50  % (26830)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.18/0.50  % (26811)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.18/0.51  % (26804)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.18/0.51  % (26804)Refutation not found, incomplete strategy% (26804)------------------------------
% 0.18/0.51  % (26804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (26804)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  
% 0.18/0.51  % (26804)Memory used [KB]: 1663
% 0.18/0.51  % (26804)Time elapsed: 0.113 s
% 0.18/0.51  % (26804)------------------------------
% 0.18/0.51  % (26804)------------------------------
% 0.18/0.51  % (26808)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.51  % (26809)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.18/0.51  % (26817)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.18/0.51  % (26812)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.18/0.51  % (26806)Refutation not found, incomplete strategy% (26806)------------------------------
% 0.18/0.51  % (26806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (26806)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  
% 0.18/0.51  % (26806)Memory used [KB]: 10746
% 0.18/0.51  % (26806)Time elapsed: 0.127 s
% 0.18/0.51  % (26806)------------------------------
% 0.18/0.51  % (26806)------------------------------
% 0.18/0.51  % (26822)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.18/0.51  % (26812)Refutation not found, incomplete strategy% (26812)------------------------------
% 0.18/0.51  % (26812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (26821)Refutation not found, incomplete strategy% (26821)------------------------------
% 0.18/0.51  % (26821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (26812)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  
% 0.18/0.51  % (26812)Memory used [KB]: 10746
% 0.18/0.51  % (26821)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  % (26812)Time elapsed: 0.131 s
% 0.18/0.51  
% 0.18/0.51  % (26812)------------------------------
% 0.18/0.51  % (26812)------------------------------
% 0.18/0.51  % (26821)Memory used [KB]: 10618
% 0.18/0.51  % (26821)Time elapsed: 0.132 s
% 0.18/0.52  % (26821)------------------------------
% 0.18/0.52  % (26821)------------------------------
% 0.18/0.52  % (26810)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.18/0.52  % (26833)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.18/0.52  % (26816)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.52  % (26813)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.18/0.52  % (26813)Refutation not found, incomplete strategy% (26813)------------------------------
% 0.18/0.52  % (26813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.52  % (26813)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.52  
% 0.18/0.52  % (26813)Memory used [KB]: 10618
% 0.18/0.52  % (26813)Time elapsed: 0.139 s
% 0.18/0.52  % (26813)------------------------------
% 0.18/0.52  % (26813)------------------------------
% 0.18/0.52  % (26820)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.18/0.52  % (26823)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.18/0.53  % (26828)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.18/0.53  % (26805)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.18/0.53  % (26834)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.18/0.53  % (26829)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.18/0.53  % (26827)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.18/0.54  % (26824)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.18/0.54  % (26826)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.18/0.54  % (26826)Refutation not found, incomplete strategy% (26826)------------------------------
% 0.18/0.54  % (26826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.54  % (26826)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.54  
% 0.18/0.54  % (26826)Memory used [KB]: 10746
% 0.18/0.54  % (26826)Time elapsed: 0.149 s
% 0.18/0.54  % (26826)------------------------------
% 0.18/0.54  % (26826)------------------------------
% 0.18/0.55  % (26818)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.18/0.55  % (26831)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.18/0.55  % (26811)Refutation found. Thanks to Tanya!
% 0.18/0.55  % SZS status Theorem for theBenchmark
% 1.67/0.57  % SZS output start Proof for theBenchmark
% 1.67/0.57  fof(f501,plain,(
% 1.67/0.57    $false),
% 1.67/0.57    inference(subsumption_resolution,[],[f500,f133])).
% 1.67/0.57  fof(f133,plain,(
% 1.67/0.57    sK3 != k2_xboole_0(sK3,k2_tarski(sK2,sK4))),
% 1.67/0.57    inference(superposition,[],[f57,f128])).
% 1.67/0.57  fof(f128,plain,(
% 1.67/0.57    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 1.67/0.57    inference(superposition,[],[f102,f61])).
% 1.67/0.57  fof(f61,plain,(
% 1.67/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.67/0.57    inference(cnf_transformation,[],[f17])).
% 1.67/0.57  fof(f17,axiom,(
% 1.67/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.67/0.57  fof(f102,plain,(
% 1.67/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) )),
% 1.67/0.57    inference(superposition,[],[f61,f60])).
% 1.67/0.57  fof(f60,plain,(
% 1.67/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f13])).
% 1.67/0.57  fof(f13,axiom,(
% 1.67/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.67/0.57  fof(f57,plain,(
% 1.67/0.57    sK3 != k2_xboole_0(k2_tarski(sK2,sK4),sK3)),
% 1.67/0.57    inference(cnf_transformation,[],[f33])).
% 1.67/0.57  fof(f33,plain,(
% 1.67/0.57    sK3 != k2_xboole_0(k2_tarski(sK2,sK4),sK3) & r2_hidden(sK4,sK3) & r2_hidden(sK2,sK3)),
% 1.67/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f32])).
% 1.67/0.57  fof(f32,plain,(
% 1.67/0.57    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (sK3 != k2_xboole_0(k2_tarski(sK2,sK4),sK3) & r2_hidden(sK4,sK3) & r2_hidden(sK2,sK3))),
% 1.67/0.57    introduced(choice_axiom,[])).
% 1.67/0.57  fof(f23,plain,(
% 1.67/0.57    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 1.67/0.57    inference(flattening,[],[f22])).
% 1.67/0.57  fof(f22,plain,(
% 1.67/0.57    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 1.67/0.57    inference(ennf_transformation,[],[f20])).
% 1.67/0.57  fof(f20,negated_conjecture,(
% 1.67/0.57    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 1.67/0.57    inference(negated_conjecture,[],[f19])).
% 1.67/0.57  fof(f19,conjecture,(
% 1.67/0.57    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 1.67/0.57  fof(f500,plain,(
% 1.67/0.57    sK3 = k2_xboole_0(sK3,k2_tarski(sK2,sK4))),
% 1.67/0.57    inference(forward_demodulation,[],[f490,f59])).
% 1.67/0.57  fof(f59,plain,(
% 1.67/0.57    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.67/0.57    inference(cnf_transformation,[],[f9])).
% 1.67/0.57  fof(f9,axiom,(
% 1.67/0.57    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.67/0.57  fof(f490,plain,(
% 1.67/0.57    k2_xboole_0(sK3,k2_tarski(sK2,sK4)) = k2_xboole_0(sK3,k1_xboole_0)),
% 1.67/0.57    inference(superposition,[],[f64,f439])).
% 1.67/0.57  fof(f439,plain,(
% 1.67/0.57    k1_xboole_0 = k4_xboole_0(k2_tarski(sK2,sK4),sK3)),
% 1.67/0.57    inference(backward_demodulation,[],[f275,f435])).
% 1.67/0.57  fof(f435,plain,(
% 1.67/0.57    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 1.67/0.57    inference(backward_demodulation,[],[f141,f424])).
% 1.67/0.57  fof(f424,plain,(
% 1.67/0.57    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(X7,X7)) )),
% 1.67/0.57    inference(resolution,[],[f420,f317])).
% 1.67/0.57  fof(f317,plain,(
% 1.67/0.57    ( ! [X17] : (r2_hidden(sK6(X17,k1_xboole_0),X17) | k1_xboole_0 = X17) )),
% 1.67/0.57    inference(resolution,[],[f70,f208])).
% 1.67/0.57  fof(f208,plain,(
% 1.67/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.67/0.57    inference(condensation,[],[f205])).
% 1.67/0.57  fof(f205,plain,(
% 1.67/0.57    ( ! [X4,X3] : (~r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,X4)) )),
% 1.67/0.57    inference(resolution,[],[f77,f181])).
% 1.67/0.57  fof(f181,plain,(
% 1.67/0.57    ( ! [X3] : (sP0(X3,k1_xboole_0,k1_xboole_0)) )),
% 1.67/0.57    inference(backward_demodulation,[],[f154,f174])).
% 1.67/0.57  fof(f174,plain,(
% 1.67/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.67/0.57    inference(superposition,[],[f172,f142])).
% 1.67/0.57  fof(f142,plain,(
% 1.67/0.57    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,X1)) )),
% 1.67/0.57    inference(superposition,[],[f140,f140])).
% 1.67/0.57  fof(f140,plain,(
% 1.67/0.57    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.67/0.57    inference(superposition,[],[f63,f106])).
% 1.67/0.57  fof(f106,plain,(
% 1.67/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.67/0.57    inference(resolution,[],[f68,f58])).
% 1.67/0.57  fof(f58,plain,(
% 1.67/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f11])).
% 1.67/0.57  fof(f11,axiom,(
% 1.67/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.67/0.57  fof(f68,plain,(
% 1.67/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.67/0.57    inference(cnf_transformation,[],[f25])).
% 1.67/0.57  fof(f25,plain,(
% 1.67/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.67/0.57    inference(ennf_transformation,[],[f10])).
% 1.67/0.57  fof(f10,axiom,(
% 1.67/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.67/0.57  fof(f63,plain,(
% 1.67/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.67/0.57    inference(cnf_transformation,[],[f8])).
% 1.67/0.57  fof(f8,axiom,(
% 1.67/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.67/0.57  fof(f172,plain,(
% 1.67/0.57    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) )),
% 1.67/0.57    inference(forward_demodulation,[],[f166,f130])).
% 1.67/0.57  fof(f130,plain,(
% 1.67/0.57    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.67/0.57    inference(superposition,[],[f128,f59])).
% 1.67/0.57  fof(f166,plain,(
% 1.67/0.57    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6)) )),
% 1.67/0.57    inference(superposition,[],[f64,f130])).
% 1.67/0.57  fof(f154,plain,(
% 1.67/0.57    ( ! [X2,X3] : (sP0(X3,k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) )),
% 1.67/0.57    inference(superposition,[],[f144,f142])).
% 1.67/0.57  fof(f144,plain,(
% 1.67/0.57    ( ! [X0] : (sP0(X0,k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 1.67/0.57    inference(forward_demodulation,[],[f143,f141])).
% 1.67/0.57  fof(f143,plain,(
% 1.67/0.57    ( ! [X0] : (sP0(X0,k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 1.67/0.57    inference(superposition,[],[f98,f140])).
% 1.67/0.57  fof(f98,plain,(
% 1.67/0.57    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 1.67/0.57    inference(equality_resolution,[],[f82])).
% 1.67/0.57  fof(f82,plain,(
% 1.67/0.57    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.67/0.57    inference(cnf_transformation,[],[f46])).
% 1.67/0.57  fof(f46,plain,(
% 1.67/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.67/0.57    inference(nnf_transformation,[],[f29])).
% 1.67/0.57  fof(f29,plain,(
% 1.67/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.67/0.57    inference(definition_folding,[],[f4,f28])).
% 1.67/0.57  fof(f28,plain,(
% 1.67/0.57    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.67/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.67/0.57  fof(f4,axiom,(
% 1.67/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.67/0.57  fof(f77,plain,(
% 1.67/0.57    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f45])).
% 1.67/0.57  fof(f45,plain,(
% 1.67/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK7(X0,X1,X2),X1)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.67/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f43,f44])).
% 1.67/0.57  fof(f44,plain,(
% 1.67/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK7(X0,X1,X2),X1)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.67/0.57    introduced(choice_axiom,[])).
% 1.67/0.57  fof(f43,plain,(
% 1.67/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.67/0.57    inference(rectify,[],[f42])).
% 1.67/0.57  fof(f42,plain,(
% 1.67/0.57    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.67/0.57    inference(flattening,[],[f41])).
% 1.67/0.57  fof(f41,plain,(
% 1.67/0.57    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.67/0.57    inference(nnf_transformation,[],[f28])).
% 1.67/0.57  fof(f70,plain,(
% 1.67/0.57    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | r2_hidden(sK6(X0,X1),X0) | X0 = X1) )),
% 1.67/0.57    inference(cnf_transformation,[],[f38])).
% 1.67/0.57  fof(f38,plain,(
% 1.67/0.57    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK6(X0,X1),X1) | ~r2_hidden(sK6(X0,X1),X0)) & (r2_hidden(sK6(X0,X1),X1) | r2_hidden(sK6(X0,X1),X0))))),
% 1.67/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).
% 1.67/0.57  fof(f37,plain,(
% 1.67/0.57    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK6(X0,X1),X1) | ~r2_hidden(sK6(X0,X1),X0)) & (r2_hidden(sK6(X0,X1),X1) | r2_hidden(sK6(X0,X1),X0))))),
% 1.67/0.57    introduced(choice_axiom,[])).
% 1.67/0.57  fof(f36,plain,(
% 1.67/0.57    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.67/0.57    inference(nnf_transformation,[],[f27])).
% 1.67/0.57  fof(f27,plain,(
% 1.67/0.57    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.67/0.57    inference(ennf_transformation,[],[f5])).
% 1.67/0.57  fof(f5,axiom,(
% 1.67/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.67/0.57  fof(f420,plain,(
% 1.67/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1))) )),
% 1.67/0.57    inference(condensation,[],[f417])).
% 1.67/0.57  fof(f417,plain,(
% 1.67/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X2,X2))) )),
% 1.67/0.57    inference(resolution,[],[f413,f67])).
% 1.67/0.57  fof(f67,plain,(
% 1.67/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f35])).
% 1.67/0.57  fof(f35,plain,(
% 1.67/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.67/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f34])).
% 1.67/0.57  fof(f34,plain,(
% 1.67/0.57    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.67/0.57    introduced(choice_axiom,[])).
% 1.67/0.57  fof(f24,plain,(
% 1.67/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.67/0.57    inference(ennf_transformation,[],[f21])).
% 1.67/0.57  fof(f21,plain,(
% 1.67/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.67/0.57    inference(rectify,[],[f6])).
% 1.67/0.57  fof(f6,axiom,(
% 1.67/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.67/0.57  fof(f413,plain,(
% 1.67/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 1.67/0.57    inference(duplicate_literal_removal,[],[f406])).
% 1.67/0.57  fof(f406,plain,(
% 1.67/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X0),X1) | r1_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 1.67/0.57    inference(resolution,[],[f215,f200])).
% 1.67/0.57  fof(f200,plain,(
% 1.67/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK5(k4_xboole_0(X0,X1),X2),X0) | r1_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 1.67/0.57    inference(resolution,[],[f197,f65])).
% 1.67/0.57  fof(f65,plain,(
% 1.67/0.57    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f35])).
% 1.67/0.57  fof(f197,plain,(
% 1.67/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | r2_hidden(X0,X1)) )),
% 1.67/0.57    inference(resolution,[],[f76,f98])).
% 1.67/0.57  fof(f76,plain,(
% 1.67/0.57    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f45])).
% 1.76/0.57  fof(f215,plain,(
% 1.76/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK5(k4_xboole_0(X0,X1),X2),X1) | r1_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 1.76/0.57    inference(resolution,[],[f204,f65])).
% 1.76/0.57  fof(f204,plain,(
% 1.76/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | ~r2_hidden(X0,X2)) )),
% 1.76/0.57    inference(resolution,[],[f77,f98])).
% 1.76/0.57  fof(f141,plain,(
% 1.76/0.57    ( ! [X1] : (k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)) )),
% 1.76/0.57    inference(superposition,[],[f63,f107])).
% 1.76/0.57  fof(f107,plain,(
% 1.76/0.57    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 1.76/0.57    inference(resolution,[],[f68,f96])).
% 1.76/0.57  fof(f96,plain,(
% 1.76/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.76/0.57    inference(equality_resolution,[],[f73])).
% 1.76/0.57  fof(f73,plain,(
% 1.76/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.76/0.57    inference(cnf_transformation,[],[f40])).
% 1.76/0.57  fof(f40,plain,(
% 1.76/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.76/0.57    inference(flattening,[],[f39])).
% 1.76/0.57  fof(f39,plain,(
% 1.76/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.76/0.57    inference(nnf_transformation,[],[f7])).
% 1.76/0.57  fof(f7,axiom,(
% 1.76/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.76/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.76/0.57  fof(f275,plain,(
% 1.76/0.57    k4_xboole_0(k2_tarski(sK2,sK4),sK3) = k5_xboole_0(k2_tarski(sK2,sK4),k2_tarski(sK2,sK4))),
% 1.76/0.57    inference(superposition,[],[f63,f252])).
% 1.76/0.57  fof(f252,plain,(
% 1.76/0.57    k2_tarski(sK2,sK4) = k3_xboole_0(k2_tarski(sK2,sK4),sK3)),
% 1.76/0.57    inference(resolution,[],[f242,f68])).
% 1.76/0.57  fof(f242,plain,(
% 1.76/0.57    r1_tarski(k2_tarski(sK2,sK4),sK3)),
% 1.76/0.57    inference(resolution,[],[f239,f56])).
% 1.76/0.57  fof(f56,plain,(
% 1.76/0.57    r2_hidden(sK4,sK3)),
% 1.76/0.57    inference(cnf_transformation,[],[f33])).
% 1.76/0.57  fof(f239,plain,(
% 1.76/0.57    ( ! [X12] : (~r2_hidden(X12,sK3) | r1_tarski(k2_tarski(sK2,X12),sK3)) )),
% 1.76/0.57    inference(resolution,[],[f94,f55])).
% 1.76/0.57  fof(f55,plain,(
% 1.76/0.57    r2_hidden(sK2,sK3)),
% 1.76/0.57    inference(cnf_transformation,[],[f33])).
% 1.76/0.57  fof(f94,plain,(
% 1.76/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.76/0.57    inference(cnf_transformation,[],[f54])).
% 1.76/0.57  fof(f54,plain,(
% 1.76/0.57    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.76/0.57    inference(flattening,[],[f53])).
% 1.76/0.57  fof(f53,plain,(
% 1.76/0.57    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.76/0.57    inference(nnf_transformation,[],[f18])).
% 1.76/0.57  fof(f18,axiom,(
% 1.76/0.57    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.76/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.76/0.57  fof(f64,plain,(
% 1.76/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.76/0.57    inference(cnf_transformation,[],[f12])).
% 1.76/0.57  fof(f12,axiom,(
% 1.76/0.57    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.76/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.76/0.57  % SZS output end Proof for theBenchmark
% 1.76/0.57  % (26811)------------------------------
% 1.76/0.57  % (26811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.57  % (26811)Termination reason: Refutation
% 1.76/0.57  
% 1.76/0.57  % (26811)Memory used [KB]: 6652
% 1.76/0.57  % (26811)Time elapsed: 0.162 s
% 1.76/0.57  % (26811)------------------------------
% 1.76/0.57  % (26811)------------------------------
% 1.76/0.57  % (26803)Success in time 0.223 s
%------------------------------------------------------------------------------

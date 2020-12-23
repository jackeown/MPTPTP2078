%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:02 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 940 expanded)
%              Number of leaves         :   13 ( 250 expanded)
%              Depth                    :   17
%              Number of atoms          :  279 (3957 expanded)
%              Number of equality atoms :   38 ( 323 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f539,plain,(
    $false ),
    inference(subsumption_resolution,[],[f531,f536])).

fof(f536,plain,(
    ! [X0] : r2_hidden(sK4(sK0,sK1,k1_xboole_0),k2_xboole_0(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f525,f69])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f525,plain,(
    r2_hidden(sK4(sK0,sK1,k1_xboole_0),sK2) ),
    inference(unit_resulting_resolution,[],[f217,f220,f306])).

fof(f306,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(resolution,[],[f188,f70])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f188,plain,(
    ! [X3] :
      ( r2_hidden(X3,k2_xboole_0(sK1,sK2))
      | ~ r2_hidden(X3,sK0) ) ),
    inference(superposition,[],[f69,f79])).

fof(f79,plain,(
    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f36,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f36,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f220,plain,(
    ~ r2_hidden(sK4(sK0,sK1,k1_xboole_0),sK1) ),
    inference(unit_resulting_resolution,[],[f74,f201,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
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
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
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
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f201,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f196,f72])).

fof(f72,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f37,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

% (27904)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f37,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f196,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,k3_xboole_0(sK0,sK2)) ) ),
    inference(superposition,[],[f67,f191])).

fof(f191,plain,(
    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f184,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f184,plain,(
    r1_tarski(k3_xboole_0(sK0,sK2),sK2) ),
    inference(superposition,[],[f41,f130])).

fof(f130,plain,(
    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f123,f122])).

fof(f122,plain,(
    k3_xboole_0(sK0,sK2) = k2_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f72,f76,f76,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f71,f44])).

fof(f71,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f37,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f123,plain,(
    k3_xboole_0(sK2,sK0) = k2_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f76,f76,f76,f58])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f38,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f217,plain,(
    r2_hidden(sK4(sK0,sK1,k1_xboole_0),sK0) ),
    inference(unit_resulting_resolution,[],[f74,f201,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f531,plain,(
    ~ r2_hidden(sK4(sK0,sK1,k1_xboole_0),k2_xboole_0(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f71,f217,f525,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_vampire %s %d
% 0.16/0.36  % Computer   : n007.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % WCLimit    : 600
% 0.16/0.36  % DateTime   : Tue Dec  1 14:06:21 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.23/0.49  % (27906)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.23/0.49  % (27917)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.23/0.49  % (27909)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.23/0.50  % (27915)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.23/0.50  % (27908)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.23/0.51  % (27913)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.23/0.51  % (27914)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.51  % (27917)Refutation found. Thanks to Tanya!
% 0.23/0.51  % SZS status Theorem for theBenchmark
% 0.23/0.51  % SZS output start Proof for theBenchmark
% 0.23/0.51  fof(f539,plain,(
% 0.23/0.51    $false),
% 0.23/0.51    inference(subsumption_resolution,[],[f531,f536])).
% 0.23/0.51  fof(f536,plain,(
% 0.23/0.51    ( ! [X0] : (r2_hidden(sK4(sK0,sK1,k1_xboole_0),k2_xboole_0(sK2,X0))) )),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f525,f69])).
% 0.23/0.51  fof(f69,plain,(
% 0.23/0.51    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.23/0.51    inference(equality_resolution,[],[f56])).
% 0.23/0.51  fof(f56,plain,(
% 0.23/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.23/0.51    inference(cnf_transformation,[],[f35])).
% 0.23/0.51  fof(f35,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).
% 0.23/0.51  fof(f34,plain,(
% 0.23/0.51    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f33,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.23/0.51    inference(rectify,[],[f32])).
% 0.23/0.51  fof(f32,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.23/0.51    inference(flattening,[],[f31])).
% 0.23/0.51  fof(f31,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.23/0.51    inference(nnf_transformation,[],[f2])).
% 0.23/0.51  fof(f2,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.23/0.51  fof(f525,plain,(
% 0.23/0.51    r2_hidden(sK4(sK0,sK1,k1_xboole_0),sK2)),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f217,f220,f306])).
% 0.23/0.51  fof(f306,plain,(
% 0.23/0.51    ( ! [X3] : (r2_hidden(X3,sK2) | r2_hidden(X3,sK1) | ~r2_hidden(X3,sK0)) )),
% 0.23/0.51    inference(resolution,[],[f188,f70])).
% 0.23/0.51  fof(f70,plain,(
% 0.23/0.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_xboole_0(X0,X1)) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 0.23/0.51    inference(equality_resolution,[],[f55])).
% 0.23/0.51  fof(f55,plain,(
% 0.23/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.23/0.51    inference(cnf_transformation,[],[f35])).
% 0.23/0.51  fof(f188,plain,(
% 0.23/0.51    ( ! [X3] : (r2_hidden(X3,k2_xboole_0(sK1,sK2)) | ~r2_hidden(X3,sK0)) )),
% 0.23/0.51    inference(superposition,[],[f69,f79])).
% 0.23/0.51  fof(f79,plain,(
% 0.23/0.51    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f36,f45])).
% 0.23/0.51  fof(f45,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.23/0.51    inference(cnf_transformation,[],[f18])).
% 0.23/0.51  fof(f18,plain,(
% 0.23/0.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.23/0.51    inference(ennf_transformation,[],[f8])).
% 0.23/0.51  fof(f8,axiom,(
% 0.23/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.23/0.51  fof(f36,plain,(
% 0.23/0.51    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.23/0.51    inference(cnf_transformation,[],[f22])).
% 0.23/0.51  fof(f22,plain,(
% 0.23/0.51    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f21])).
% 0.23/0.51  fof(f21,plain,(
% 0.23/0.51    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f16,plain,(
% 0.23/0.51    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.23/0.51    inference(flattening,[],[f15])).
% 0.23/0.51  fof(f15,plain,(
% 0.23/0.51    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.23/0.51    inference(ennf_transformation,[],[f13])).
% 0.23/0.51  fof(f13,negated_conjecture,(
% 0.23/0.51    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.23/0.51    inference(negated_conjecture,[],[f12])).
% 0.23/0.51  fof(f12,conjecture,(
% 0.23/0.51    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.23/0.51  fof(f220,plain,(
% 0.23/0.51    ~r2_hidden(sK4(sK0,sK1,k1_xboole_0),sK1)),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f74,f201,f53])).
% 0.23/0.51  fof(f53,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f30])).
% 0.23/0.51  fof(f30,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 0.23/0.51  fof(f29,plain,(
% 0.23/0.51    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f28,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.23/0.51    inference(rectify,[],[f27])).
% 0.23/0.51  fof(f27,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.23/0.51    inference(flattening,[],[f26])).
% 0.23/0.51  fof(f26,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.23/0.51    inference(nnf_transformation,[],[f3])).
% 0.23/0.51  fof(f3,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.23/0.51  fof(f201,plain,(
% 0.23/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.23/0.51    inference(subsumption_resolution,[],[f196,f72])).
% 0.23/0.51  fof(f72,plain,(
% 0.23/0.51    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK2))) )),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f37,f44])).
% 0.23/0.51  fof(f44,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f24])).
% 0.23/0.51  fof(f24,plain,(
% 0.23/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f23])).
% 0.23/0.51  fof(f23,plain,(
% 0.23/0.51    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f17,plain,(
% 0.23/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.23/0.51    inference(ennf_transformation,[],[f14])).
% 0.23/0.51  fof(f14,plain,(
% 0.23/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.23/0.51    inference(rectify,[],[f5])).
% 0.23/0.51  fof(f5,axiom,(
% 0.23/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.23/0.51  % (27904)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.23/0.51  fof(f37,plain,(
% 0.23/0.51    r1_xboole_0(sK0,sK2)),
% 0.23/0.51    inference(cnf_transformation,[],[f22])).
% 0.23/0.51  fof(f196,plain,(
% 0.23/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,k3_xboole_0(sK0,sK2))) )),
% 0.23/0.51    inference(superposition,[],[f67,f191])).
% 0.23/0.51  fof(f191,plain,(
% 0.23/0.51    k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK2),sK2)),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f184,f48])).
% 0.23/0.51  fof(f48,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.23/0.51    inference(cnf_transformation,[],[f25])).
% 0.23/0.51  fof(f25,plain,(
% 0.23/0.51    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.23/0.51    inference(nnf_transformation,[],[f7])).
% 0.23/0.51  fof(f7,axiom,(
% 0.23/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.23/0.51  fof(f184,plain,(
% 0.23/0.51    r1_tarski(k3_xboole_0(sK0,sK2),sK2)),
% 0.23/0.51    inference(superposition,[],[f41,f130])).
% 0.23/0.51  fof(f130,plain,(
% 0.23/0.51    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK2,sK0)),
% 0.23/0.51    inference(backward_demodulation,[],[f123,f122])).
% 0.23/0.51  fof(f122,plain,(
% 0.23/0.51    k3_xboole_0(sK0,sK2) = k2_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK0))),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f72,f76,f76,f58])).
% 0.23/0.51  fof(f58,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 0.23/0.51    inference(cnf_transformation,[],[f35])).
% 0.23/0.51  fof(f76,plain,(
% 0.23/0.51    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK2,sK0))) )),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f71,f44])).
% 0.23/0.51  fof(f71,plain,(
% 0.23/0.51    r1_xboole_0(sK2,sK0)),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f37,f46])).
% 0.23/0.51  fof(f46,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f19])).
% 0.23/0.51  fof(f19,plain,(
% 0.23/0.51    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.23/0.51    inference(ennf_transformation,[],[f4])).
% 0.23/0.51  fof(f4,axiom,(
% 0.23/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.23/0.51  fof(f123,plain,(
% 0.23/0.51    k3_xboole_0(sK2,sK0) = k2_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK0))),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f76,f76,f76,f58])).
% 0.23/0.51  fof(f41,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f9])).
% 0.23/0.51  fof(f9,axiom,(
% 0.23/0.51    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.23/0.51  fof(f67,plain,(
% 0.23/0.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 0.23/0.51    inference(equality_resolution,[],[f49])).
% 0.23/0.51  fof(f49,plain,(
% 0.23/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.23/0.51    inference(cnf_transformation,[],[f30])).
% 0.23/0.51  fof(f74,plain,(
% 0.23/0.51    k1_xboole_0 != k4_xboole_0(sK0,sK1)),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f38,f47])).
% 0.23/0.51  fof(f47,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f25])).
% 0.23/0.51  fof(f38,plain,(
% 0.23/0.51    ~r1_tarski(sK0,sK1)),
% 0.23/0.51    inference(cnf_transformation,[],[f22])).
% 0.23/0.51  fof(f217,plain,(
% 0.23/0.51    r2_hidden(sK4(sK0,sK1,k1_xboole_0),sK0)),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f74,f201,f52])).
% 0.23/0.51  fof(f52,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.23/0.51    inference(cnf_transformation,[],[f30])).
% 0.23/0.51  fof(f531,plain,(
% 0.23/0.51    ~r2_hidden(sK4(sK0,sK1,k1_xboole_0),k2_xboole_0(sK2,sK0))),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f71,f217,f525,f64])).
% 0.23/0.51  fof(f64,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f20])).
% 0.23/0.51  fof(f20,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.23/0.51    inference(ennf_transformation,[],[f6])).
% 0.23/0.51  fof(f6,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).
% 0.23/0.51  % SZS output end Proof for theBenchmark
% 0.23/0.51  % (27917)------------------------------
% 0.23/0.51  % (27917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (27917)Termination reason: Refutation
% 0.23/0.51  
% 0.23/0.51  % (27917)Memory used [KB]: 6524
% 0.23/0.51  % (27917)Time elapsed: 0.028 s
% 0.23/0.51  % (27917)------------------------------
% 0.23/0.51  % (27917)------------------------------
% 0.23/0.52  % (27899)Success in time 0.141 s
%------------------------------------------------------------------------------

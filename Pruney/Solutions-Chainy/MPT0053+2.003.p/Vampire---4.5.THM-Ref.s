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
% DateTime   : Thu Dec  3 12:29:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 635 expanded)
%              Number of leaves         :    6 ( 154 expanded)
%              Depth                    :   23
%              Number of atoms          :  170 (4162 expanded)
%              Number of equality atoms :   27 ( 658 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(subsumption_resolution,[],[f235,f202])).

fof(f202,plain,(
    ! [X0] : ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X0) ),
    inference(subsumption_resolution,[],[f201,f185])).

fof(f185,plain,(
    ! [X0,X1] : ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f184,f17])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f184,plain,(
    ! [X0,X1] : ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0))) ),
    inference(condensation,[],[f183])).

fof(f183,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X2,k2_xboole_0(X3,k1_xboole_0)))
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X4) ) ),
    inference(subsumption_resolution,[],[f172,f86])).

fof(f86,plain,(
    ! [X2,X1] : ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X1,k2_xboole_0(sK0,X2))) ),
    inference(forward_demodulation,[],[f79,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f79,plain,(
    ! [X2,X1] : ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(k4_xboole_0(X1,sK0),X2)) ),
    inference(resolution,[],[f63,f29])).

fof(f29,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f63,plain,(
    ! [X0] : ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,sK0)) ),
    inference(condensation,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X2,X3))
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X4,sK0)) ) ),
    inference(forward_demodulation,[],[f56,f17])).

fof(f56,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X2,k2_xboole_0(X3,k1_xboole_0)))
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X4,sK0)) ) ),
    inference(superposition,[],[f46,f20])).

fof(f46,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X2,k1_xboole_0))
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X1,sK0)) ) ),
    inference(resolution,[],[f37,f28])).

fof(f28,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,sK0)) ) ),
    inference(resolution,[],[f33,f28])).

fof(f33,plain,
    ( r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),sK0)
    | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),X0),sK0)
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f16,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1))
   => k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f172,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X2,k2_xboole_0(X3,k1_xboole_0)))
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X4,k2_xboole_0(sK0,sK1)))
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X4) ) ),
    inference(superposition,[],[f51,f20])).

fof(f51,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X4,k1_xboole_0))
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X5,k2_xboole_0(sK0,sK1)))
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X5) ) ),
    inference(resolution,[],[f40,f27])).

fof(f27,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k2_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f34,f28])).

fof(f34,plain,
    ( r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k2_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X1] :
      ( k1_xboole_0 != X1
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),X1),k2_xboole_0(sK0,sK1))
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),X1),X1) ) ),
    inference(superposition,[],[f16,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f201,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(sK0,sK1),X1)))
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X0) ) ),
    inference(condensation,[],[f200])).

fof(f200,plain,(
    ! [X6,X7,X5] :
      ( r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X5)
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X6,k4_xboole_0(k2_xboole_0(sK0,sK1),X7)))
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X6) ) ),
    inference(subsumption_resolution,[],[f194,f185])).

fof(f194,plain,(
    ! [X6,X7,X5] :
      ( r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X5)
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(k1_xboole_0,X5))
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X6,k4_xboole_0(k2_xboole_0(sK0,sK1),X7)))
      | ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X6) ) ),
    inference(resolution,[],[f70,f27])).

fof(f70,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(k2_xboole_0(sK0,sK1),X3))
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X2)
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(k1_xboole_0,X2)) ) ),
    inference(resolution,[],[f41,f29])).

fof(f41,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k2_xboole_0(sK0,sK1))
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(k1_xboole_0,X1))
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X1) ) ),
    inference(resolution,[],[f34,f27])).

fof(f235,plain,(
    ! [X10] : r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X10) ),
    inference(subsumption_resolution,[],[f234,f185])).

fof(f234,plain,(
    ! [X10] :
      ( r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(k1_xboole_0,X10))
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X10) ) ),
    inference(subsumption_resolution,[],[f221,f202])).

fof(f221,plain,(
    ! [X10,X9] :
      ( r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k2_xboole_0(X9,sK0))
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(k1_xboole_0,X10))
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X10) ) ),
    inference(resolution,[],[f66,f82])).

% (7044)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f82,plain,(
    ! [X2,X1] : ~ r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X1,k2_xboole_0(X2,sK0))) ),
    inference(superposition,[],[f63,f20])).

fof(f66,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(sK0,X3))
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X3)
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(k1_xboole_0,X4))
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X4) ) ),
    inference(resolution,[],[f38,f27])).

fof(f38,plain,(
    ! [X1] :
      ( r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0)
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(sK0,X1))
      | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X1) ) ),
    inference(resolution,[],[f33,f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:47:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (7032)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (7040)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (7040)Refutation not found, incomplete strategy% (7040)------------------------------
% 0.21/0.47  % (7040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (7040)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (7040)Memory used [KB]: 6012
% 0.21/0.47  % (7040)Time elapsed: 0.067 s
% 0.21/0.47  % (7040)------------------------------
% 0.21/0.47  % (7040)------------------------------
% 0.21/0.48  % (7041)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (7028)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (7033)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (7028)Refutation not found, incomplete strategy% (7028)------------------------------
% 0.21/0.48  % (7028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (7028)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (7028)Memory used [KB]: 10490
% 0.21/0.48  % (7028)Time elapsed: 0.070 s
% 0.21/0.48  % (7028)------------------------------
% 0.21/0.48  % (7028)------------------------------
% 0.21/0.49  % (7027)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (7029)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (7025)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (7025)Refutation not found, incomplete strategy% (7025)------------------------------
% 0.21/0.49  % (7025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7025)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7025)Memory used [KB]: 6012
% 0.21/0.49  % (7025)Time elapsed: 0.079 s
% 0.21/0.49  % (7025)------------------------------
% 0.21/0.49  % (7025)------------------------------
% 0.21/0.50  % (7038)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (7038)Refutation not found, incomplete strategy% (7038)------------------------------
% 0.21/0.50  % (7038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7038)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (7038)Memory used [KB]: 1535
% 0.21/0.50  % (7038)Time elapsed: 0.084 s
% 0.21/0.50  % (7038)------------------------------
% 0.21/0.50  % (7038)------------------------------
% 0.21/0.50  % (7036)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (7030)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (7026)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (7037)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (7026)Refutation not found, incomplete strategy% (7026)------------------------------
% 0.21/0.50  % (7026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7026)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (7026)Memory used [KB]: 10490
% 0.21/0.50  % (7026)Time elapsed: 0.091 s
% 0.21/0.50  % (7026)------------------------------
% 0.21/0.50  % (7026)------------------------------
% 0.21/0.50  % (7037)Refutation not found, incomplete strategy% (7037)------------------------------
% 0.21/0.50  % (7037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7037)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (7037)Memory used [KB]: 6012
% 0.21/0.50  % (7037)Time elapsed: 0.001 s
% 0.21/0.50  % (7037)------------------------------
% 0.21/0.50  % (7037)------------------------------
% 0.21/0.50  % (7043)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (7029)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f235,f202])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f201,f185])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f184,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)))) )),
% 0.21/0.50    inference(condensation,[],[f183])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ( ! [X4,X2,X3] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X2,k2_xboole_0(X3,k1_xboole_0))) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X4)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f172,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X1,k2_xboole_0(sK0,X2)))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f79,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(k4_xboole_0(X1,sK0),X2))) )),
% 0.21/0.50    inference(resolution,[],[f63,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(rectify,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,sK0))) )),
% 0.21/0.50    inference(condensation,[],[f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X4,X2,X3] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X2,X3)) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X4,sK0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f56,f17])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X4,X2,X3] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X2,k2_xboole_0(X3,k1_xboole_0))) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X4,sK0))) )),
% 0.21/0.50    inference(superposition,[],[f46,f20])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X2,k1_xboole_0)) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X1,sK0))) )),
% 0.21/0.50    inference(resolution,[],[f37,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,sK0))) )),
% 0.21/0.50    inference(resolution,[],[f33,f28])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),sK0) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0)),
% 0.21/0.50    inference(equality_resolution,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 != X0 | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),X0),X0)) )),
% 0.21/0.50    inference(superposition,[],[f16,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1)) => k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.50    inference(negated_conjecture,[],[f6])).
% 0.21/0.50  fof(f6,conjecture,(
% 0.21/0.50    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    ( ! [X4,X2,X3] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X2,k2_xboole_0(X3,k1_xboole_0))) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X4,k2_xboole_0(sK0,sK1))) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X4)) )),
% 0.21/0.50    inference(superposition,[],[f51,f20])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X4,X5] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X4,k1_xboole_0)) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X5,k2_xboole_0(sK0,sK1))) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X5)) )),
% 0.21/0.50    inference(resolution,[],[f40,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k2_xboole_0(sK0,sK1)) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.50    inference(resolution,[],[f34,f28])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k2_xboole_0(sK0,sK1))),
% 0.21/0.50    inference(equality_resolution,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X1] : (k1_xboole_0 != X1 | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),X1),k2_xboole_0(sK0,sK1)) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),X1),X1)) )),
% 0.21/0.50    inference(superposition,[],[f16,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(sK0,sK1),X1))) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X0)) )),
% 0.21/0.50    inference(condensation,[],[f200])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    ( ! [X6,X7,X5] : (r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X5) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X6,k4_xboole_0(k2_xboole_0(sK0,sK1),X7))) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X6)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f194,f185])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    ( ! [X6,X7,X5] : (r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X5) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(k1_xboole_0,X5)) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X6,k4_xboole_0(k2_xboole_0(sK0,sK1),X7))) | ~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X6)) )),
% 0.21/0.50    inference(resolution,[],[f70,f27])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(k2_xboole_0(sK0,sK1),X3)) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X2) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(k1_xboole_0,X2))) )),
% 0.21/0.50    inference(resolution,[],[f41,f29])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k2_xboole_0(sK0,sK1)) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(k1_xboole_0,X1)) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X1)) )),
% 0.21/0.50    inference(resolution,[],[f34,f27])).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    ( ! [X10] : (r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X10)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f234,f185])).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    ( ! [X10] : (r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(k1_xboole_0,X10)) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X10)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f221,f202])).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    ( ! [X10,X9] : (r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k2_xboole_0(X9,sK0)) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(k1_xboole_0,X10)) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X10)) )),
% 0.21/0.50    inference(resolution,[],[f66,f82])).
% 0.21/0.50  % (7044)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X1,k2_xboole_0(X2,sK0)))) )),
% 0.21/0.50    inference(superposition,[],[f63,f20])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X4,X3] : (r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(sK0,X3)) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X3) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(k1_xboole_0,X4)) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X4)) )),
% 0.21/0.50    inference(resolution,[],[f38,f27])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X1] : (r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(sK0,X1)) | r2_hidden(sK2(sK0,k2_xboole_0(sK0,sK1),k1_xboole_0),X1)) )),
% 0.21/0.50    inference(resolution,[],[f33,f27])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (7029)------------------------------
% 0.21/0.50  % (7029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7029)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (7029)Memory used [KB]: 1791
% 0.21/0.50  % (7029)Time elapsed: 0.092 s
% 0.21/0.50  % (7029)------------------------------
% 0.21/0.50  % (7029)------------------------------
% 0.21/0.50  % (7035)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (7024)Success in time 0.148 s
%------------------------------------------------------------------------------

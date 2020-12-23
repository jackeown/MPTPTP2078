%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 353 expanded)
%              Number of leaves         :   20 ( 106 expanded)
%              Depth                    :   20
%              Number of atoms          :  344 (1630 expanded)
%              Number of equality atoms :  138 ( 734 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f469,plain,(
    $false ),
    inference(equality_resolution,[],[f468])).

fof(f468,plain,(
    ! [X24] : sK1 != X24 ),
    inference(subsumption_resolution,[],[f467,f138])).

fof(f138,plain,(
    k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f44,f137])).

fof(f137,plain,(
    k1_xboole_0 != sK1 ),
    inference(equality_resolution,[],[f136])).

fof(f136,plain,(
    ! [X0] :
      ( sK1 != X0
      | k1_xboole_0 != X0 ) ),
    inference(subsumption_resolution,[],[f135,f48])).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f135,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | sK1 != X0
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f132,f111])).

fof(f111,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(sK3(X0))
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f102,f58])).

fof(f58,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X2] :
          ( np__1 = k1_funct_1(sK3(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK3(X0)) = X0
      & v1_funct_1(sK3(X0))
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( np__1 = k1_funct_1(sK3(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK3(X0)) = X0
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(f102,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(sK3(X0))
      | k1_xboole_0 = k2_relat_1(sK3(X0)) ) ),
    inference(resolution,[],[f50,f56])).

fof(f56,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f132,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3(X0)),sK0)
      | sK1 != X0 ) ),
    inference(forward_demodulation,[],[f131,f58])).

fof(f131,plain,(
    ! [X0] :
      ( sK1 != k1_relat_1(sK3(X0))
      | ~ r1_tarski(k2_relat_1(sK3(X0)),sK0) ) ),
    inference(subsumption_resolution,[],[f129,f56])).

fof(f129,plain,(
    ! [X0] :
      ( sK1 != k1_relat_1(sK3(X0))
      | ~ r1_tarski(k2_relat_1(sK3(X0)),sK0)
      | ~ v1_relat_1(sK3(X0)) ) ),
    inference(resolution,[],[f45,f57])).

fof(f57,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X2] :
      ( ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK1
      | ~ r1_tarski(k2_relat_1(X2),sK0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK0)
          | k1_relat_1(X2) != sK1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK0 ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f44,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f467,plain,(
    ! [X24] :
      ( k1_xboole_0 = sK0
      | sK1 != X24 ) ),
    inference(resolution,[],[f448,f393])).

fof(f393,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | sK1 != X1 ) ),
    inference(resolution,[],[f391,f378])).

fof(f378,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | sK1 != X0 ) ),
    inference(subsumption_resolution,[],[f377,f136])).

fof(f377,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | sK1 != X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f371,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
          & k1_relat_1(sK2(X0,X1)) = X0
          & v1_funct_1(sK2(X0,X1))
          & v1_relat_1(sK2(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
        & k1_relat_1(sK2(X0,X1)) = X0
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(f371,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK2(X0,X1)),sK0)
      | sK1 != X0 ) ),
    inference(subsumption_resolution,[],[f370,f136])).

fof(f370,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK2(X0,X1)),sK0)
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f369])).

fof(f369,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK2(X0,X1)),sK0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f133,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f133,plain,(
    ! [X2,X1] :
      ( sK1 != k1_relat_1(sK2(X1,X2))
      | ~ r1_tarski(k2_relat_1(sK2(X1,X2)),sK0)
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f130,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f130,plain,(
    ! [X2,X1] :
      ( sK1 != k1_relat_1(sK2(X1,X2))
      | ~ r1_tarski(k2_relat_1(sK2(X1,X2)),sK0)
      | ~ v1_relat_1(sK2(X1,X2))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f45,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f391,plain,(
    ! [X3] :
      ( r1_tarski(k1_tarski(X3),sK0)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(superposition,[],[f65,f385])).

fof(f385,plain,(
    ! [X0] : sK5(k1_tarski(X0),sK0) = X0 ),
    inference(equality_resolution,[],[f379])).

fof(f379,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK5(k1_tarski(X1),sK0) = X1 ) ),
    inference(resolution,[],[f378,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | sK5(k1_tarski(X0),X1) = X0 ) ),
    inference(resolution,[],[f64,f76])).

fof(f76,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f448,plain,(
    ! [X21] :
      ( r2_hidden(sK7(k1_xboole_0,X21),X21)
      | k1_xboole_0 = X21 ) ),
    inference(forward_demodulation,[],[f438,f47])).

fof(f47,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f438,plain,(
    ! [X21] :
      ( k2_relat_1(k1_xboole_0) = X21
      | r2_hidden(sK7(k1_xboole_0,X21),X21) ) ),
    inference(resolution,[],[f72,f91])).

fof(f91,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f62,f49])).

fof(f49,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f39,f42,f41,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (19980)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.48  % (19997)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (19980)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f469,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(equality_resolution,[],[f468])).
% 0.20/0.52  fof(f468,plain,(
% 0.20/0.52    ( ! [X24] : (sK1 != X24) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f467,f138])).
% 0.20/0.53  fof(f138,plain,(
% 0.20/0.53    k1_xboole_0 != sK0),
% 0.20/0.53    inference(subsumption_resolution,[],[f44,f137])).
% 0.20/0.53  fof(f137,plain,(
% 0.20/0.53    k1_xboole_0 != sK1),
% 0.20/0.53    inference(equality_resolution,[],[f136])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    ( ! [X0] : (sK1 != X0 | k1_xboole_0 != X0) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f135,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,sK0) | sK1 != X0 | k1_xboole_0 != X0) )),
% 0.20/0.53    inference(superposition,[],[f132,f111])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK3(X0)) | k1_xboole_0 != X0) )),
% 0.20/0.53    inference(superposition,[],[f102,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0] : (! [X2] : (np__1 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (np__1 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 != k1_relat_1(sK3(X0)) | k1_xboole_0 = k2_relat_1(sK3(X0))) )),
% 0.20/0.53    inference(resolution,[],[f50,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.20/0.53  fof(f132,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3(X0)),sK0) | sK1 != X0) )),
% 0.20/0.53    inference(forward_demodulation,[],[f131,f58])).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    ( ! [X0] : (sK1 != k1_relat_1(sK3(X0)) | ~r1_tarski(k2_relat_1(sK3(X0)),sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f129,f56])).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    ( ! [X0] : (sK1 != k1_relat_1(sK3(X0)) | ~r1_tarski(k2_relat_1(sK3(X0)),sK0) | ~v1_relat_1(sK3(X0))) )),
% 0.20/0.53    inference(resolution,[],[f45,f57])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X2] : (~v1_funct_1(X2) | k1_relat_1(X2) != sK1 | ~r1_tarski(k2_relat_1(X2),sK0) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.20/0.53    inference(flattening,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.20/0.53    inference(negated_conjecture,[],[f11])).
% 0.20/0.53  fof(f11,conjecture,(
% 0.20/0.53    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f467,plain,(
% 0.20/0.53    ( ! [X24] : (k1_xboole_0 = sK0 | sK1 != X24) )),
% 0.20/0.53    inference(resolution,[],[f448,f393])).
% 0.20/0.53  fof(f393,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | sK1 != X1) )),
% 0.20/0.53    inference(resolution,[],[f391,f378])).
% 0.20/0.53  fof(f378,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | sK1 != X0) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f377,f136])).
% 0.20/0.53  fof(f377,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | sK1 != X0 | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(superposition,[],[f371,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | k1_xboole_0 = X0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).
% 0.20/0.53  fof(f371,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK2(X0,X1)),sK0) | sK1 != X0) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f370,f136])).
% 0.20/0.53  fof(f370,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK2(X0,X1)),sK0) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f369])).
% 0.20/0.53  fof(f369,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK2(X0,X1)),sK0) | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(superposition,[],[f133,f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    ( ! [X2,X1] : (sK1 != k1_relat_1(sK2(X1,X2)) | ~r1_tarski(k2_relat_1(sK2(X1,X2)),sK0) | k1_xboole_0 = X1) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f130,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f130,plain,(
% 0.20/0.53    ( ! [X2,X1] : (sK1 != k1_relat_1(sK2(X1,X2)) | ~r1_tarski(k2_relat_1(sK2(X1,X2)),sK0) | ~v1_relat_1(sK2(X1,X2)) | k1_xboole_0 = X1) )),
% 0.20/0.53    inference(resolution,[],[f45,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f391,plain,(
% 0.20/0.53    ( ! [X3] : (r1_tarski(k1_tarski(X3),sK0) | ~r2_hidden(X3,sK0)) )),
% 0.20/0.53    inference(superposition,[],[f65,f385])).
% 0.20/0.53  fof(f385,plain,(
% 0.20/0.53    ( ! [X0] : (sK5(k1_tarski(X0),sK0) = X0) )),
% 0.20/0.53    inference(equality_resolution,[],[f379])).
% 0.20/0.53  fof(f379,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sK1 != X0 | sK5(k1_tarski(X1),sK0) = X1) )),
% 0.20/0.53    inference(resolution,[],[f378,f83])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | sK5(k1_tarski(X0),X1) = X0) )),
% 0.20/0.53    inference(resolution,[],[f64,f76])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.20/0.53    inference(equality_resolution,[],[f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.53    inference(rectify,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(rectify,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f448,plain,(
% 0.20/0.53    ( ! [X21] : (r2_hidden(sK7(k1_xboole_0,X21),X21) | k1_xboole_0 = X21) )),
% 0.20/0.53    inference(forward_demodulation,[],[f438,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.53  fof(f438,plain,(
% 0.20/0.53    ( ! [X21] : (k2_relat_1(k1_xboole_0) = X21 | r2_hidden(sK7(k1_xboole_0,X21),X21)) )),
% 0.20/0.53    inference(resolution,[],[f72,f91])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(condensation,[],[f90])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(resolution,[],[f62,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.53    inference(rectify,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) | k2_relat_1(X0) = X1 | r2_hidden(sK7(X0,X1),X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f39,f42,f41,f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.53    inference(rectify,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (19980)------------------------------
% 0.20/0.53  % (19980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (19980)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (19980)Memory used [KB]: 6908
% 0.20/0.53  % (19980)Time elapsed: 0.112 s
% 0.20/0.53  % (19980)------------------------------
% 0.20/0.53  % (19980)------------------------------
% 0.20/0.53  % (19965)Success in time 0.171 s
%------------------------------------------------------------------------------

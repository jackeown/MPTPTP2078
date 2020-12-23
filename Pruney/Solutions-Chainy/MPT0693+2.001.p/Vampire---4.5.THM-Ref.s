%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:58 EST 2020

% Result     : Theorem 4.53s
% Output     : Refutation 4.94s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 155 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :   18
%              Number of atoms          :  311 ( 644 expanded)
%              Number of equality atoms :   76 ( 162 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4105,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4102,f168])).

fof(f168,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f73,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f52,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f4102,plain,(
    k3_xboole_0(sK0,k2_relat_1(sK1)) != k3_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(superposition,[],[f79,f3685])).

fof(f3685,plain,(
    ! [X0] : k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k3_xboole_0(k2_relat_1(sK1),X0) ),
    inference(backward_demodulation,[],[f138,f3417])).

fof(f3417,plain,(
    ! [X2] : k10_relat_1(sK1,X2) = k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,X2)) ),
    inference(superposition,[],[f168,f668])).

fof(f668,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k3_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f667,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f667,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,X0) = k3_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1))
      | ~ r2_hidden(sK3(k10_relat_1(sK1,X0),k1_relat_1(sK1),k10_relat_1(sK1,X0)),k10_relat_1(sK1,X0)) ) ),
    inference(duplicate_literal_removal,[],[f653])).

fof(f653,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,X0) = k3_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1))
      | k10_relat_1(sK1,X0) = k3_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1))
      | ~ r2_hidden(sK3(k10_relat_1(sK1,X0),k1_relat_1(sK1),k10_relat_1(sK1,X0)),k10_relat_1(sK1,X0))
      | ~ r2_hidden(sK3(k10_relat_1(sK1,X0),k1_relat_1(sK1),k10_relat_1(sK1,X0)),k10_relat_1(sK1,X0)) ) ),
    inference(resolution,[],[f176,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f176,plain,(
    ! [X12,X13] :
      ( r2_hidden(sK3(k10_relat_1(sK1,X12),X13,k10_relat_1(sK1,X12)),k1_relat_1(sK1))
      | k10_relat_1(sK1,X12) = k3_xboole_0(k10_relat_1(sK1,X12),X13) ) ),
    inference(resolution,[],[f96,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(sK1,X1))
      | r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f82,f39])).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(sK1,X1))
      | r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f67,f40])).

fof(f40,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
                | ~ r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
                  & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
            & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(f138,plain,(
    ! [X0] : k3_xboole_0(k2_relat_1(sK1),X0) = k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,X0))) ),
    inference(backward_demodulation,[],[f131,f133])).

fof(f133,plain,(
    ! [X0] : k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0)) = k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,X0)) ),
    inference(superposition,[],[f89,f77])).

fof(f77,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f42,f39])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f89,plain,(
    ! [X0,X1] : k10_relat_1(sK1,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f88,f39])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k10_relat_1(sK1,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f58,f40])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

fof(f131,plain,(
    ! [X0] : k3_xboole_0(k2_relat_1(sK1),X0) = k9_relat_1(sK1,k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))) ),
    inference(resolution,[],[f87,f75])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f57,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f87,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK1))
      | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f86,f39])).

fof(f86,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK1))
      | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f53,f40])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f79,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k2_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f41,f78])).

fof(f78,plain,(
    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
    inference(resolution,[],[f43,f39])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f41,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:33:00 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.19/0.44  % (30783)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.44  % (30784)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.45  % (30786)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.46  % (30803)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.46  % (30809)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.47  % (30801)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.47  % (30799)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.47  % (30792)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.48  % (30796)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.48  % (30794)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.48  % (30791)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.48  % (30807)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.48  % (30792)Refutation not found, incomplete strategy% (30792)------------------------------
% 0.19/0.48  % (30792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (30792)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (30792)Memory used [KB]: 10746
% 0.19/0.48  % (30792)Time elapsed: 0.115 s
% 0.19/0.48  % (30792)------------------------------
% 0.19/0.48  % (30792)------------------------------
% 0.19/0.49  % (30811)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.49  % (30811)Refutation not found, incomplete strategy% (30811)------------------------------
% 0.19/0.49  % (30811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (30811)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (30811)Memory used [KB]: 1663
% 0.19/0.49  % (30811)Time elapsed: 0.122 s
% 0.19/0.49  % (30811)------------------------------
% 0.19/0.49  % (30811)------------------------------
% 0.19/0.50  % (30788)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.51  % (30804)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.51  % (30787)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.51  % (30782)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.51  % (30785)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.52  % (30810)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.52  % (30810)Refutation not found, incomplete strategy% (30810)------------------------------
% 0.19/0.52  % (30810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (30810)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (30810)Memory used [KB]: 10746
% 0.19/0.52  % (30810)Time elapsed: 0.141 s
% 0.19/0.52  % (30810)------------------------------
% 0.19/0.52  % (30810)------------------------------
% 0.19/0.52  % (30806)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.52  % (30808)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.52  % (30802)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.53  % (30798)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.53  % (30798)Refutation not found, incomplete strategy% (30798)------------------------------
% 0.19/0.53  % (30798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (30798)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (30798)Memory used [KB]: 10618
% 0.19/0.53  % (30798)Time elapsed: 0.149 s
% 0.19/0.53  % (30798)------------------------------
% 0.19/0.53  % (30798)------------------------------
% 0.19/0.53  % (30800)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.53  % (30795)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.53  % (30790)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.53  % (30793)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.55  % (30805)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.56  % (30797)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.57  % (30789)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.97/0.63  % (30815)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.35/0.65  % (30817)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.35/0.66  % (30817)Refutation not found, incomplete strategy% (30817)------------------------------
% 2.35/0.66  % (30817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.35/0.66  % (30817)Termination reason: Refutation not found, incomplete strategy
% 2.35/0.66  
% 2.35/0.66  % (30817)Memory used [KB]: 6140
% 2.35/0.66  % (30817)Time elapsed: 0.103 s
% 2.35/0.66  % (30817)------------------------------
% 2.35/0.66  % (30817)------------------------------
% 2.35/0.66  % (30818)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.35/0.67  % (30816)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.35/0.67  % (30785)Refutation not found, incomplete strategy% (30785)------------------------------
% 2.35/0.67  % (30785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.35/0.67  % (30785)Termination reason: Refutation not found, incomplete strategy
% 2.35/0.67  
% 2.35/0.67  % (30785)Memory used [KB]: 6140
% 2.35/0.67  % (30785)Time elapsed: 0.286 s
% 2.35/0.67  % (30785)------------------------------
% 2.35/0.67  % (30785)------------------------------
% 3.27/0.77  % (30784)Time limit reached!
% 3.27/0.77  % (30784)------------------------------
% 3.27/0.77  % (30784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.77  % (30784)Termination reason: Time limit
% 3.27/0.77  
% 3.27/0.77  % (30784)Memory used [KB]: 8571
% 3.27/0.77  % (30784)Time elapsed: 0.407 s
% 3.27/0.77  % (30784)------------------------------
% 3.27/0.77  % (30784)------------------------------
% 3.27/0.78  % (30819)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.27/0.80  % (30806)Time limit reached!
% 3.27/0.80  % (30806)------------------------------
% 3.27/0.80  % (30806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.80  % (30806)Termination reason: Time limit
% 3.27/0.80  
% 3.27/0.80  % (30806)Memory used [KB]: 13816
% 3.27/0.80  % (30806)Time elapsed: 0.418 s
% 3.27/0.80  % (30806)------------------------------
% 3.27/0.80  % (30806)------------------------------
% 3.27/0.81  % (30820)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 3.82/0.88  % (30821)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.07/0.91  % (30796)Time limit reached!
% 4.07/0.91  % (30796)------------------------------
% 4.07/0.91  % (30796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.07/0.91  % (30788)Time limit reached!
% 4.07/0.91  % (30788)------------------------------
% 4.07/0.91  % (30788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.07/0.91  % (30788)Termination reason: Time limit
% 4.07/0.91  % (30788)Termination phase: Saturation
% 4.07/0.91  
% 4.07/0.91  % (30788)Memory used [KB]: 14200
% 4.07/0.91  % (30788)Time elapsed: 0.500 s
% 4.07/0.91  % (30788)------------------------------
% 4.07/0.91  % (30788)------------------------------
% 4.07/0.91  % (30796)Termination reason: Time limit
% 4.07/0.91  
% 4.07/0.91  % (30796)Memory used [KB]: 5756
% 4.07/0.91  % (30796)Time elapsed: 0.523 s
% 4.07/0.91  % (30796)------------------------------
% 4.07/0.91  % (30796)------------------------------
% 4.07/0.93  % (30825)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 4.53/0.99  % (30789)Refutation found. Thanks to Tanya!
% 4.53/0.99  % SZS status Theorem for theBenchmark
% 4.94/1.02  % SZS output start Proof for theBenchmark
% 4.94/1.02  fof(f4105,plain,(
% 4.94/1.02    $false),
% 4.94/1.02    inference(subsumption_resolution,[],[f4102,f168])).
% 4.94/1.02  fof(f168,plain,(
% 4.94/1.02    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 4.94/1.02    inference(superposition,[],[f73,f52])).
% 4.94/1.02  fof(f52,plain,(
% 4.94/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.94/1.02    inference(cnf_transformation,[],[f6])).
% 4.94/1.02  fof(f6,axiom,(
% 4.94/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.94/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 4.94/1.02  fof(f73,plain,(
% 4.94/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 4.94/1.02    inference(superposition,[],[f52,f50])).
% 4.94/1.02  fof(f50,plain,(
% 4.94/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 4.94/1.02    inference(cnf_transformation,[],[f4])).
% 4.94/1.02  fof(f4,axiom,(
% 4.94/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 4.94/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 4.94/1.02  fof(f4102,plain,(
% 4.94/1.02    k3_xboole_0(sK0,k2_relat_1(sK1)) != k3_xboole_0(k2_relat_1(sK1),sK0)),
% 4.94/1.02    inference(superposition,[],[f79,f3685])).
% 4.94/1.02  fof(f3685,plain,(
% 4.94/1.02    ( ! [X0] : (k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k3_xboole_0(k2_relat_1(sK1),X0)) )),
% 4.94/1.02    inference(backward_demodulation,[],[f138,f3417])).
% 4.94/1.02  fof(f3417,plain,(
% 4.94/1.02    ( ! [X2] : (k10_relat_1(sK1,X2) = k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,X2))) )),
% 4.94/1.02    inference(superposition,[],[f168,f668])).
% 4.94/1.02  fof(f668,plain,(
% 4.94/1.02    ( ! [X0] : (k10_relat_1(sK1,X0) = k3_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 4.94/1.02    inference(subsumption_resolution,[],[f667,f96])).
% 4.94/1.02  fof(f96,plain,(
% 4.94/1.02    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k3_xboole_0(X0,X1) = X0) )),
% 4.94/1.02    inference(factoring,[],[f62])).
% 4.94/1.02  fof(f62,plain,(
% 4.94/1.02    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 4.94/1.02    inference(cnf_transformation,[],[f38])).
% 4.94/1.02  fof(f38,plain,(
% 4.94/1.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.94/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 4.94/1.02  fof(f37,plain,(
% 4.94/1.02    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 4.94/1.02    introduced(choice_axiom,[])).
% 4.94/1.02  fof(f36,plain,(
% 4.94/1.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.94/1.02    inference(rectify,[],[f35])).
% 4.94/1.02  fof(f35,plain,(
% 4.94/1.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.94/1.02    inference(flattening,[],[f34])).
% 4.94/1.02  fof(f34,plain,(
% 4.94/1.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.94/1.02    inference(nnf_transformation,[],[f1])).
% 4.94/1.02  fof(f1,axiom,(
% 4.94/1.02    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.94/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 4.94/1.02  fof(f667,plain,(
% 4.94/1.02    ( ! [X0] : (k10_relat_1(sK1,X0) = k3_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)) | ~r2_hidden(sK3(k10_relat_1(sK1,X0),k1_relat_1(sK1),k10_relat_1(sK1,X0)),k10_relat_1(sK1,X0))) )),
% 4.94/1.02    inference(duplicate_literal_removal,[],[f653])).
% 4.94/1.02  fof(f653,plain,(
% 4.94/1.02    ( ! [X0] : (k10_relat_1(sK1,X0) = k3_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)) | k10_relat_1(sK1,X0) = k3_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)) | ~r2_hidden(sK3(k10_relat_1(sK1,X0),k1_relat_1(sK1),k10_relat_1(sK1,X0)),k10_relat_1(sK1,X0)) | ~r2_hidden(sK3(k10_relat_1(sK1,X0),k1_relat_1(sK1),k10_relat_1(sK1,X0)),k10_relat_1(sK1,X0))) )),
% 4.94/1.02    inference(resolution,[],[f176,f64])).
% 4.94/1.02  fof(f64,plain,(
% 4.94/1.02    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 4.94/1.02    inference(cnf_transformation,[],[f38])).
% 4.94/1.02  fof(f176,plain,(
% 4.94/1.02    ( ! [X12,X13] : (r2_hidden(sK3(k10_relat_1(sK1,X12),X13,k10_relat_1(sK1,X12)),k1_relat_1(sK1)) | k10_relat_1(sK1,X12) = k3_xboole_0(k10_relat_1(sK1,X12),X13)) )),
% 4.94/1.02    inference(resolution,[],[f96,f83])).
% 4.94/1.02  fof(f83,plain,(
% 4.94/1.02    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK1,X1)) | r2_hidden(X0,k1_relat_1(sK1))) )),
% 4.94/1.02    inference(subsumption_resolution,[],[f82,f39])).
% 4.94/1.02  fof(f39,plain,(
% 4.94/1.02    v1_relat_1(sK1)),
% 4.94/1.02    inference(cnf_transformation,[],[f26])).
% 4.94/1.02  fof(f26,plain,(
% 4.94/1.02    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 4.94/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f25])).
% 4.94/1.02  fof(f25,plain,(
% 4.94/1.02    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & v1_funct_1(X1) & v1_relat_1(X1)) => (k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 4.94/1.02    introduced(choice_axiom,[])).
% 4.94/1.02  fof(f15,plain,(
% 4.94/1.02    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 4.94/1.02    inference(flattening,[],[f14])).
% 4.94/1.02  fof(f14,plain,(
% 4.94/1.02    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 4.94/1.02    inference(ennf_transformation,[],[f13])).
% 4.94/1.02  fof(f13,negated_conjecture,(
% 4.94/1.02    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 4.94/1.02    inference(negated_conjecture,[],[f12])).
% 4.94/1.02  fof(f12,conjecture,(
% 4.94/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 4.94/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 4.94/1.02  fof(f82,plain,(
% 4.94/1.02    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK1,X1)) | r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 4.94/1.02    inference(resolution,[],[f67,f40])).
% 4.94/1.02  fof(f40,plain,(
% 4.94/1.02    v1_funct_1(sK1)),
% 4.94/1.02    inference(cnf_transformation,[],[f26])).
% 4.94/1.02  fof(f67,plain,(
% 4.94/1.02    ( ! [X4,X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(X4,k10_relat_1(X0,X1)) | r2_hidden(X4,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 4.94/1.02    inference(equality_resolution,[],[f44])).
% 4.94/1.02  fof(f44,plain,(
% 4.94/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,X2) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.94/1.02    inference(cnf_transformation,[],[f31])).
% 4.94/1.02  fof(f31,plain,(
% 4.94/1.02    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((~r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.94/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 4.94/1.02  fof(f30,plain,(
% 4.94/1.02    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((~r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 4.94/1.02    introduced(choice_axiom,[])).
% 4.94/1.02  fof(f29,plain,(
% 4.94/1.02    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.94/1.02    inference(rectify,[],[f28])).
% 4.94/1.02  fof(f28,plain,(
% 4.94/1.02    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.94/1.02    inference(flattening,[],[f27])).
% 4.94/1.02  fof(f27,plain,(
% 4.94/1.02    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.94/1.02    inference(nnf_transformation,[],[f19])).
% 4.94/1.02  fof(f19,plain,(
% 4.94/1.02    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.94/1.02    inference(flattening,[],[f18])).
% 4.94/1.02  fof(f18,plain,(
% 4.94/1.02    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.94/1.02    inference(ennf_transformation,[],[f9])).
% 4.94/1.02  fof(f9,axiom,(
% 4.94/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 4.94/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).
% 4.94/1.02  fof(f138,plain,(
% 4.94/1.02    ( ! [X0] : (k3_xboole_0(k2_relat_1(sK1),X0) = k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,X0)))) )),
% 4.94/1.02    inference(backward_demodulation,[],[f131,f133])).
% 4.94/1.02  fof(f133,plain,(
% 4.94/1.02    ( ! [X0] : (k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0)) = k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,X0))) )),
% 4.94/1.02    inference(superposition,[],[f89,f77])).
% 4.94/1.02  fof(f77,plain,(
% 4.94/1.02    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 4.94/1.02    inference(resolution,[],[f42,f39])).
% 4.94/1.02  fof(f42,plain,(
% 4.94/1.02    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 4.94/1.02    inference(cnf_transformation,[],[f16])).
% 4.94/1.02  fof(f16,plain,(
% 4.94/1.02    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 4.94/1.02    inference(ennf_transformation,[],[f8])).
% 4.94/1.02  fof(f8,axiom,(
% 4.94/1.02    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 4.94/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 4.94/1.02  fof(f89,plain,(
% 4.94/1.02    ( ! [X0,X1] : (k10_relat_1(sK1,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 4.94/1.02    inference(subsumption_resolution,[],[f88,f39])).
% 4.94/1.02  fof(f88,plain,(
% 4.94/1.02    ( ! [X0,X1] : (k10_relat_1(sK1,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 4.94/1.02    inference(resolution,[],[f58,f40])).
% 4.94/1.02  fof(f58,plain,(
% 4.94/1.02    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 4.94/1.02    inference(cnf_transformation,[],[f24])).
% 4.94/1.02  fof(f24,plain,(
% 4.94/1.02    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.94/1.02    inference(flattening,[],[f23])).
% 4.94/1.02  fof(f23,plain,(
% 4.94/1.02    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.94/1.02    inference(ennf_transformation,[],[f10])).
% 4.94/1.02  fof(f10,axiom,(
% 4.94/1.02    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 4.94/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).
% 4.94/1.02  fof(f131,plain,(
% 4.94/1.02    ( ! [X0] : (k3_xboole_0(k2_relat_1(sK1),X0) = k9_relat_1(sK1,k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0)))) )),
% 4.94/1.02    inference(resolution,[],[f87,f75])).
% 4.94/1.02  fof(f75,plain,(
% 4.94/1.02    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 4.94/1.02    inference(resolution,[],[f57,f68])).
% 4.94/1.02  fof(f68,plain,(
% 4.94/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.94/1.02    inference(equality_resolution,[],[f55])).
% 4.94/1.02  fof(f55,plain,(
% 4.94/1.02    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.94/1.02    inference(cnf_transformation,[],[f33])).
% 4.94/1.02  fof(f33,plain,(
% 4.94/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.94/1.02    inference(flattening,[],[f32])).
% 4.94/1.02  fof(f32,plain,(
% 4.94/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.94/1.02    inference(nnf_transformation,[],[f2])).
% 4.94/1.02  fof(f2,axiom,(
% 4.94/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.94/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.94/1.02  fof(f57,plain,(
% 4.94/1.02    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1)) )),
% 4.94/1.02    inference(cnf_transformation,[],[f22])).
% 4.94/1.02  fof(f22,plain,(
% 4.94/1.02    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 4.94/1.02    inference(ennf_transformation,[],[f3])).
% 4.94/1.02  fof(f3,axiom,(
% 4.94/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 4.94/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 4.94/1.02  fof(f87,plain,(
% 4.94/1.02    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0) )),
% 4.94/1.02    inference(subsumption_resolution,[],[f86,f39])).
% 4.94/1.02  fof(f86,plain,(
% 4.94/1.02    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 | ~v1_relat_1(sK1)) )),
% 4.94/1.02    inference(resolution,[],[f53,f40])).
% 4.94/1.02  fof(f53,plain,(
% 4.94/1.02    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 4.94/1.02    inference(cnf_transformation,[],[f21])).
% 4.94/1.02  fof(f21,plain,(
% 4.94/1.02    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.94/1.02    inference(flattening,[],[f20])).
% 4.94/1.02  fof(f20,plain,(
% 4.94/1.02    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.94/1.02    inference(ennf_transformation,[],[f11])).
% 4.94/1.02  fof(f11,axiom,(
% 4.94/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 4.94/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 4.94/1.02  fof(f79,plain,(
% 4.94/1.02    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k2_relat_1(sK1))),
% 4.94/1.02    inference(backward_demodulation,[],[f41,f78])).
% 4.94/1.02  fof(f78,plain,(
% 4.94/1.02    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)),
% 4.94/1.02    inference(resolution,[],[f43,f39])).
% 4.94/1.02  fof(f43,plain,(
% 4.94/1.02    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 4.94/1.02    inference(cnf_transformation,[],[f17])).
% 4.94/1.02  fof(f17,plain,(
% 4.94/1.02    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 4.94/1.02    inference(ennf_transformation,[],[f7])).
% 4.94/1.02  fof(f7,axiom,(
% 4.94/1.02    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 4.94/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 4.94/1.02  fof(f41,plain,(
% 4.94/1.02    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))),
% 4.94/1.02    inference(cnf_transformation,[],[f26])).
% 4.94/1.02  % SZS output end Proof for theBenchmark
% 4.94/1.02  % (30789)------------------------------
% 4.94/1.02  % (30789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.94/1.02  % (30789)Termination reason: Refutation
% 4.94/1.02  
% 4.94/1.02  % (30789)Memory used [KB]: 4733
% 4.94/1.02  % (30789)Time elapsed: 0.521 s
% 4.94/1.02  % (30789)------------------------------
% 4.94/1.02  % (30789)------------------------------
% 4.94/1.02  % (30781)Success in time 0.674 s
%------------------------------------------------------------------------------

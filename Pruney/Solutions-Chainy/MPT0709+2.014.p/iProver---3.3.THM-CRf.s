%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:37 EST 2020

% Result     : Theorem 12.06s
% Output     : CNFRefutation 12.06s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 113 expanded)
%              Number of clauses        :   34 (  34 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  311 ( 479 expanded)
%              Number of equality atoms :   47 (  75 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f72,f63])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
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

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f33,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f34,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f46,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k10_relat_1(sK3,k9_relat_1(sK3,sK2)) != sK2
      & v2_funct_1(sK3)
      & r1_tarski(sK2,k1_relat_1(sK3))
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( k10_relat_1(sK3,k9_relat_1(sK3,sK2)) != sK2
    & v2_funct_1(sK3)
    & r1_tarski(sK2,k1_relat_1(sK3))
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f46])).

fof(f78,plain,(
    k10_relat_1(sK3,k9_relat_1(sK3,sK2)) != sK2 ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_5435,plain,
    ( r2_hidden(sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)),X1)
    | ~ r2_hidden(sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)),k4_xboole_0(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_43885,plain,
    ( r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,sK2))
    | ~ r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k4_xboole_0(k9_relat_1(sK3,sK2),k4_xboole_0(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3))))) ),
    inference(instantiation,[status(thm)],[c_5435])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k4_xboole_0(X1,k4_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_17477,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k4_xboole_0(k9_relat_1(sK3,sK2),k4_xboole_0(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3)))) = k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_347,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2126,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k9_relat_1(X2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X2,sK2)),k9_relat_1(X2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
    | X1 != k9_relat_1(X2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
    | X0 != sK0(k9_relat_1(X2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X2,sK2)) ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_5774,plain,
    ( r2_hidden(sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)),X1)
    | ~ r2_hidden(sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)),k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
    | X1 != k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
    | sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)) != sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_2126])).

cnf(c_17476,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
    | r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k4_xboole_0(k9_relat_1(sK3,sK2),k4_xboole_0(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3)))))
    | k4_xboole_0(k9_relat_1(sK3,sK2),k4_xboole_0(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3)))) != k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
    | sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) != sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_5774])).

cnf(c_344,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5775,plain,
    ( sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)) = sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_5780,plain,
    ( sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) = sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_5775])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_5409,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)),k9_relat_1(X0,sK2))
    | r1_tarski(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5415,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,sK2))
    | r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_5409])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1102,plain,
    ( r2_hidden(sK0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)),k9_relat_1(X0,X1))
    | r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1824,plain,
    ( r2_hidden(sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)),k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
    | r1_tarski(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1102])).

cnf(c_1826,plain,
    ( r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
    | r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_1824])).

cnf(c_16,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1432,plain,
    ( r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_21,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1320,plain,
    ( ~ r1_tarski(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2))
    | ~ r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),k1_relat_1(X0))
    | r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),sK2)
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1322,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2))
    | ~ r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),k1_relat_1(sK3))
    | r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1320])).

cnf(c_18,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1036,plain,
    ( r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_990,plain,
    ( ~ r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),sK2)
    | ~ r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
    | k10_relat_1(sK3,k9_relat_1(sK3,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_22,negated_conjecture,
    ( k10_relat_1(sK3,k9_relat_1(sK3,sK2)) != sK2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_23,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_26,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_43885,c_17477,c_17476,c_5780,c_5415,c_1826,c_1432,c_1322,c_1036,c_990,c_22,c_23,c_24,c_25,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:39:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 12.06/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.06/1.98  
% 12.06/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.06/1.98  
% 12.06/1.98  ------  iProver source info
% 12.06/1.98  
% 12.06/1.98  git: date: 2020-06-30 10:37:57 +0100
% 12.06/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.06/1.98  git: non_committed_changes: false
% 12.06/1.98  git: last_make_outside_of_git: false
% 12.06/1.98  
% 12.06/1.98  ------ 
% 12.06/1.98  
% 12.06/1.98  ------ Input Options
% 12.06/1.98  
% 12.06/1.98  --out_options                           all
% 12.06/1.98  --tptp_safe_out                         true
% 12.06/1.98  --problem_path                          ""
% 12.06/1.98  --include_path                          ""
% 12.06/1.98  --clausifier                            res/vclausify_rel
% 12.06/1.98  --clausifier_options                    --mode clausify
% 12.06/1.98  --stdin                                 false
% 12.06/1.98  --stats_out                             sel
% 12.06/1.98  
% 12.06/1.98  ------ General Options
% 12.06/1.98  
% 12.06/1.98  --fof                                   false
% 12.06/1.98  --time_out_real                         604.99
% 12.06/1.98  --time_out_virtual                      -1.
% 12.06/1.98  --symbol_type_check                     false
% 12.06/1.98  --clausify_out                          false
% 12.06/1.98  --sig_cnt_out                           false
% 12.06/1.98  --trig_cnt_out                          false
% 12.06/1.98  --trig_cnt_out_tolerance                1.
% 12.06/1.98  --trig_cnt_out_sk_spl                   false
% 12.06/1.98  --abstr_cl_out                          false
% 12.06/1.98  
% 12.06/1.98  ------ Global Options
% 12.06/1.98  
% 12.06/1.98  --schedule                              none
% 12.06/1.98  --add_important_lit                     false
% 12.06/1.98  --prop_solver_per_cl                    1000
% 12.06/1.98  --min_unsat_core                        false
% 12.06/1.98  --soft_assumptions                      false
% 12.06/1.98  --soft_lemma_size                       3
% 12.06/1.98  --prop_impl_unit_size                   0
% 12.06/1.98  --prop_impl_unit                        []
% 12.06/1.98  --share_sel_clauses                     true
% 12.06/1.98  --reset_solvers                         false
% 12.06/1.98  --bc_imp_inh                            [conj_cone]
% 12.06/1.98  --conj_cone_tolerance                   3.
% 12.06/1.98  --extra_neg_conj                        none
% 12.06/1.98  --large_theory_mode                     true
% 12.06/1.98  --prolific_symb_bound                   200
% 12.06/1.98  --lt_threshold                          2000
% 12.06/1.98  --clause_weak_htbl                      true
% 12.06/1.98  --gc_record_bc_elim                     false
% 12.06/1.98  
% 12.06/1.98  ------ Preprocessing Options
% 12.06/1.98  
% 12.06/1.98  --preprocessing_flag                    true
% 12.06/1.98  --time_out_prep_mult                    0.1
% 12.06/1.98  --splitting_mode                        input
% 12.06/1.98  --splitting_grd                         true
% 12.06/1.98  --splitting_cvd                         false
% 12.06/1.98  --splitting_cvd_svl                     false
% 12.06/1.98  --splitting_nvd                         32
% 12.06/1.98  --sub_typing                            true
% 12.06/1.98  --prep_gs_sim                           false
% 12.06/1.98  --prep_unflatten                        true
% 12.06/1.98  --prep_res_sim                          true
% 12.06/1.98  --prep_upred                            true
% 12.06/1.98  --prep_sem_filter                       exhaustive
% 12.06/1.98  --prep_sem_filter_out                   false
% 12.06/1.98  --pred_elim                             false
% 12.06/1.98  --res_sim_input                         true
% 12.06/1.98  --eq_ax_congr_red                       true
% 12.06/1.98  --pure_diseq_elim                       true
% 12.06/1.98  --brand_transform                       false
% 12.06/1.98  --non_eq_to_eq                          false
% 12.06/1.98  --prep_def_merge                        true
% 12.06/1.98  --prep_def_merge_prop_impl              false
% 12.06/1.98  --prep_def_merge_mbd                    true
% 12.06/1.98  --prep_def_merge_tr_red                 false
% 12.06/1.98  --prep_def_merge_tr_cl                  false
% 12.06/1.98  --smt_preprocessing                     true
% 12.06/1.98  --smt_ac_axioms                         fast
% 12.06/1.98  --preprocessed_out                      false
% 12.06/1.98  --preprocessed_stats                    false
% 12.06/1.98  
% 12.06/1.98  ------ Abstraction refinement Options
% 12.06/1.98  
% 12.06/1.98  --abstr_ref                             []
% 12.06/1.98  --abstr_ref_prep                        false
% 12.06/1.98  --abstr_ref_until_sat                   false
% 12.06/1.98  --abstr_ref_sig_restrict                funpre
% 12.06/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 12.06/1.98  --abstr_ref_under                       []
% 12.06/1.98  
% 12.06/1.98  ------ SAT Options
% 12.06/1.98  
% 12.06/1.98  --sat_mode                              false
% 12.06/1.98  --sat_fm_restart_options                ""
% 12.06/1.98  --sat_gr_def                            false
% 12.06/1.98  --sat_epr_types                         true
% 12.06/1.98  --sat_non_cyclic_types                  false
% 12.06/1.98  --sat_finite_models                     false
% 12.06/1.98  --sat_fm_lemmas                         false
% 12.06/1.98  --sat_fm_prep                           false
% 12.06/1.98  --sat_fm_uc_incr                        true
% 12.06/1.98  --sat_out_model                         small
% 12.06/1.98  --sat_out_clauses                       false
% 12.06/1.98  
% 12.06/1.98  ------ QBF Options
% 12.06/1.98  
% 12.06/1.98  --qbf_mode                              false
% 12.06/1.98  --qbf_elim_univ                         false
% 12.06/1.98  --qbf_dom_inst                          none
% 12.06/1.98  --qbf_dom_pre_inst                      false
% 12.06/1.98  --qbf_sk_in                             false
% 12.06/1.98  --qbf_pred_elim                         true
% 12.06/1.98  --qbf_split                             512
% 12.06/1.98  
% 12.06/1.98  ------ BMC1 Options
% 12.06/1.98  
% 12.06/1.98  --bmc1_incremental                      false
% 12.06/1.98  --bmc1_axioms                           reachable_all
% 12.06/1.98  --bmc1_min_bound                        0
% 12.06/1.98  --bmc1_max_bound                        -1
% 12.06/1.98  --bmc1_max_bound_default                -1
% 12.06/1.98  --bmc1_symbol_reachability              true
% 12.06/1.98  --bmc1_property_lemmas                  false
% 12.06/1.98  --bmc1_k_induction                      false
% 12.06/1.98  --bmc1_non_equiv_states                 false
% 12.06/1.98  --bmc1_deadlock                         false
% 12.06/1.98  --bmc1_ucm                              false
% 12.06/1.98  --bmc1_add_unsat_core                   none
% 12.06/1.98  --bmc1_unsat_core_children              false
% 12.06/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 12.06/1.98  --bmc1_out_stat                         full
% 12.06/1.98  --bmc1_ground_init                      false
% 12.06/1.98  --bmc1_pre_inst_next_state              false
% 12.06/1.98  --bmc1_pre_inst_state                   false
% 12.06/1.98  --bmc1_pre_inst_reach_state             false
% 12.06/1.98  --bmc1_out_unsat_core                   false
% 12.06/1.98  --bmc1_aig_witness_out                  false
% 12.06/1.98  --bmc1_verbose                          false
% 12.06/1.98  --bmc1_dump_clauses_tptp                false
% 12.06/1.98  --bmc1_dump_unsat_core_tptp             false
% 12.06/1.98  --bmc1_dump_file                        -
% 12.06/1.98  --bmc1_ucm_expand_uc_limit              128
% 12.06/1.98  --bmc1_ucm_n_expand_iterations          6
% 12.06/1.98  --bmc1_ucm_extend_mode                  1
% 12.06/1.98  --bmc1_ucm_init_mode                    2
% 12.06/1.98  --bmc1_ucm_cone_mode                    none
% 12.06/1.98  --bmc1_ucm_reduced_relation_type        0
% 12.06/1.98  --bmc1_ucm_relax_model                  4
% 12.06/1.98  --bmc1_ucm_full_tr_after_sat            true
% 12.06/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 12.06/1.98  --bmc1_ucm_layered_model                none
% 12.06/1.98  --bmc1_ucm_max_lemma_size               10
% 12.06/1.98  
% 12.06/1.98  ------ AIG Options
% 12.06/1.98  
% 12.06/1.98  --aig_mode                              false
% 12.06/1.98  
% 12.06/1.98  ------ Instantiation Options
% 12.06/1.98  
% 12.06/1.98  --instantiation_flag                    true
% 12.06/1.98  --inst_sos_flag                         false
% 12.06/1.98  --inst_sos_phase                        true
% 12.06/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.06/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.06/1.98  --inst_lit_sel_side                     num_symb
% 12.06/1.98  --inst_solver_per_active                1400
% 12.06/1.98  --inst_solver_calls_frac                1.
% 12.06/1.98  --inst_passive_queue_type               priority_queues
% 12.06/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.06/1.98  --inst_passive_queues_freq              [25;2]
% 12.06/1.98  --inst_dismatching                      true
% 12.06/1.98  --inst_eager_unprocessed_to_passive     true
% 12.06/1.98  --inst_prop_sim_given                   true
% 12.06/1.98  --inst_prop_sim_new                     false
% 12.06/1.98  --inst_subs_new                         false
% 12.06/1.98  --inst_eq_res_simp                      false
% 12.06/1.98  --inst_subs_given                       false
% 12.06/1.98  --inst_orphan_elimination               true
% 12.06/1.98  --inst_learning_loop_flag               true
% 12.06/1.98  --inst_learning_start                   3000
% 12.06/1.98  --inst_learning_factor                  2
% 12.06/1.98  --inst_start_prop_sim_after_learn       3
% 12.06/1.98  --inst_sel_renew                        solver
% 12.06/1.98  --inst_lit_activity_flag                true
% 12.06/1.98  --inst_restr_to_given                   false
% 12.06/1.98  --inst_activity_threshold               500
% 12.06/1.98  --inst_out_proof                        true
% 12.06/1.98  
% 12.06/1.98  ------ Resolution Options
% 12.06/1.98  
% 12.06/1.98  --resolution_flag                       true
% 12.06/1.98  --res_lit_sel                           adaptive
% 12.06/1.98  --res_lit_sel_side                      none
% 12.06/1.98  --res_ordering                          kbo
% 12.06/1.98  --res_to_prop_solver                    active
% 12.06/1.98  --res_prop_simpl_new                    false
% 12.06/1.98  --res_prop_simpl_given                  true
% 12.06/1.98  --res_passive_queue_type                priority_queues
% 12.06/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.06/1.98  --res_passive_queues_freq               [15;5]
% 12.06/1.98  --res_forward_subs                      full
% 12.06/1.98  --res_backward_subs                     full
% 12.06/1.98  --res_forward_subs_resolution           true
% 12.06/1.98  --res_backward_subs_resolution          true
% 12.06/1.98  --res_orphan_elimination                true
% 12.06/1.98  --res_time_limit                        2.
% 12.06/1.98  --res_out_proof                         true
% 12.06/1.98  
% 12.06/1.98  ------ Superposition Options
% 12.06/1.98  
% 12.06/1.98  --superposition_flag                    true
% 12.06/1.98  --sup_passive_queue_type                priority_queues
% 12.06/1.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.06/1.98  --sup_passive_queues_freq               [1;4]
% 12.06/1.98  --demod_completeness_check              fast
% 12.06/1.98  --demod_use_ground                      true
% 12.06/1.98  --sup_to_prop_solver                    passive
% 12.06/1.98  --sup_prop_simpl_new                    true
% 12.06/1.98  --sup_prop_simpl_given                  true
% 12.06/1.98  --sup_fun_splitting                     false
% 12.06/1.98  --sup_smt_interval                      50000
% 12.06/1.98  
% 12.06/1.98  ------ Superposition Simplification Setup
% 12.06/1.98  
% 12.06/1.98  --sup_indices_passive                   []
% 12.06/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.06/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.06/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.06/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 12.06/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.06/1.98  --sup_full_bw                           [BwDemod]
% 12.06/1.98  --sup_immed_triv                        [TrivRules]
% 12.06/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.06/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.06/1.98  --sup_immed_bw_main                     []
% 12.06/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.06/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 12.06/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.06/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.06/1.98  
% 12.06/1.98  ------ Combination Options
% 12.06/1.98  
% 12.06/1.98  --comb_res_mult                         3
% 12.06/1.98  --comb_sup_mult                         2
% 12.06/1.98  --comb_inst_mult                        10
% 12.06/1.98  
% 12.06/1.98  ------ Debug Options
% 12.06/1.98  
% 12.06/1.98  --dbg_backtrace                         false
% 12.06/1.98  --dbg_dump_prop_clauses                 false
% 12.06/1.98  --dbg_dump_prop_clauses_file            -
% 12.06/1.98  --dbg_out_stat                          false
% 12.06/1.98  ------ Parsing...
% 12.06/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.06/1.98  
% 12.06/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 12.06/1.98  
% 12.06/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.06/1.98  
% 12.06/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.06/1.98  ------ Proving...
% 12.06/1.98  ------ Problem Properties 
% 12.06/1.98  
% 12.06/1.98  
% 12.06/1.98  clauses                                 26
% 12.06/1.98  conjectures                             5
% 12.06/1.98  EPR                                     8
% 12.06/1.98  Horn                                    21
% 12.06/1.98  unary                                   8
% 12.06/1.98  binary                                  8
% 12.06/1.98  lits                                    59
% 12.06/1.98  lits eq                                 11
% 12.06/1.98  fd_pure                                 0
% 12.06/1.98  fd_pseudo                               0
% 12.06/1.98  fd_cond                                 1
% 12.06/1.98  fd_pseudo_cond                          4
% 12.06/1.98  AC symbols                              0
% 12.06/1.98  
% 12.06/1.98  ------ Input Options Time Limit: Unbounded
% 12.06/1.98  
% 12.06/1.98  
% 12.06/1.98  ------ 
% 12.06/1.98  Current options:
% 12.06/1.98  ------ 
% 12.06/1.98  
% 12.06/1.98  ------ Input Options
% 12.06/1.98  
% 12.06/1.98  --out_options                           all
% 12.06/1.98  --tptp_safe_out                         true
% 12.06/1.98  --problem_path                          ""
% 12.06/1.98  --include_path                          ""
% 12.06/1.98  --clausifier                            res/vclausify_rel
% 12.06/1.98  --clausifier_options                    --mode clausify
% 12.06/1.98  --stdin                                 false
% 12.06/1.98  --stats_out                             sel
% 12.06/1.98  
% 12.06/1.98  ------ General Options
% 12.06/1.98  
% 12.06/1.98  --fof                                   false
% 12.06/1.98  --time_out_real                         604.99
% 12.06/1.98  --time_out_virtual                      -1.
% 12.06/1.98  --symbol_type_check                     false
% 12.06/1.98  --clausify_out                          false
% 12.06/1.98  --sig_cnt_out                           false
% 12.06/1.98  --trig_cnt_out                          false
% 12.06/1.98  --trig_cnt_out_tolerance                1.
% 12.06/1.98  --trig_cnt_out_sk_spl                   false
% 12.06/1.98  --abstr_cl_out                          false
% 12.06/1.98  
% 12.06/1.98  ------ Global Options
% 12.06/1.98  
% 12.06/1.98  --schedule                              none
% 12.06/1.98  --add_important_lit                     false
% 12.06/1.98  --prop_solver_per_cl                    1000
% 12.06/1.98  --min_unsat_core                        false
% 12.06/1.98  --soft_assumptions                      false
% 12.06/1.98  --soft_lemma_size                       3
% 12.06/1.98  --prop_impl_unit_size                   0
% 12.06/1.98  --prop_impl_unit                        []
% 12.06/1.98  --share_sel_clauses                     true
% 12.06/1.98  --reset_solvers                         false
% 12.06/1.98  --bc_imp_inh                            [conj_cone]
% 12.06/1.98  --conj_cone_tolerance                   3.
% 12.06/1.98  --extra_neg_conj                        none
% 12.06/1.98  --large_theory_mode                     true
% 12.06/1.98  --prolific_symb_bound                   200
% 12.06/1.98  --lt_threshold                          2000
% 12.06/1.98  --clause_weak_htbl                      true
% 12.06/1.98  --gc_record_bc_elim                     false
% 12.06/1.98  
% 12.06/1.98  ------ Preprocessing Options
% 12.06/1.98  
% 12.06/1.98  --preprocessing_flag                    true
% 12.06/1.98  --time_out_prep_mult                    0.1
% 12.06/1.98  --splitting_mode                        input
% 12.06/1.98  --splitting_grd                         true
% 12.06/1.98  --splitting_cvd                         false
% 12.06/1.98  --splitting_cvd_svl                     false
% 12.06/1.98  --splitting_nvd                         32
% 12.06/1.98  --sub_typing                            true
% 12.06/1.98  --prep_gs_sim                           false
% 12.06/1.98  --prep_unflatten                        true
% 12.06/1.98  --prep_res_sim                          true
% 12.06/1.98  --prep_upred                            true
% 12.06/1.98  --prep_sem_filter                       exhaustive
% 12.06/1.98  --prep_sem_filter_out                   false
% 12.06/1.98  --pred_elim                             false
% 12.06/1.98  --res_sim_input                         true
% 12.06/1.98  --eq_ax_congr_red                       true
% 12.06/1.98  --pure_diseq_elim                       true
% 12.06/1.98  --brand_transform                       false
% 12.06/1.98  --non_eq_to_eq                          false
% 12.06/1.98  --prep_def_merge                        true
% 12.06/1.98  --prep_def_merge_prop_impl              false
% 12.06/1.98  --prep_def_merge_mbd                    true
% 12.06/1.98  --prep_def_merge_tr_red                 false
% 12.06/1.98  --prep_def_merge_tr_cl                  false
% 12.06/1.98  --smt_preprocessing                     true
% 12.06/1.98  --smt_ac_axioms                         fast
% 12.06/1.98  --preprocessed_out                      false
% 12.06/1.98  --preprocessed_stats                    false
% 12.06/1.98  
% 12.06/1.98  ------ Abstraction refinement Options
% 12.06/1.98  
% 12.06/1.98  --abstr_ref                             []
% 12.06/1.98  --abstr_ref_prep                        false
% 12.06/1.98  --abstr_ref_until_sat                   false
% 12.06/1.98  --abstr_ref_sig_restrict                funpre
% 12.06/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 12.06/1.98  --abstr_ref_under                       []
% 12.06/1.98  
% 12.06/1.98  ------ SAT Options
% 12.06/1.98  
% 12.06/1.98  --sat_mode                              false
% 12.06/1.98  --sat_fm_restart_options                ""
% 12.06/1.98  --sat_gr_def                            false
% 12.06/1.98  --sat_epr_types                         true
% 12.06/1.98  --sat_non_cyclic_types                  false
% 12.06/1.98  --sat_finite_models                     false
% 12.06/1.98  --sat_fm_lemmas                         false
% 12.06/1.98  --sat_fm_prep                           false
% 12.06/1.98  --sat_fm_uc_incr                        true
% 12.06/1.98  --sat_out_model                         small
% 12.06/1.98  --sat_out_clauses                       false
% 12.06/1.98  
% 12.06/1.98  ------ QBF Options
% 12.06/1.98  
% 12.06/1.98  --qbf_mode                              false
% 12.06/1.98  --qbf_elim_univ                         false
% 12.06/1.98  --qbf_dom_inst                          none
% 12.06/1.98  --qbf_dom_pre_inst                      false
% 12.06/1.98  --qbf_sk_in                             false
% 12.06/1.98  --qbf_pred_elim                         true
% 12.06/1.98  --qbf_split                             512
% 12.06/1.98  
% 12.06/1.98  ------ BMC1 Options
% 12.06/1.98  
% 12.06/1.98  --bmc1_incremental                      false
% 12.06/1.98  --bmc1_axioms                           reachable_all
% 12.06/1.98  --bmc1_min_bound                        0
% 12.06/1.98  --bmc1_max_bound                        -1
% 12.06/1.98  --bmc1_max_bound_default                -1
% 12.06/1.98  --bmc1_symbol_reachability              true
% 12.06/1.98  --bmc1_property_lemmas                  false
% 12.06/1.98  --bmc1_k_induction                      false
% 12.06/1.98  --bmc1_non_equiv_states                 false
% 12.06/1.98  --bmc1_deadlock                         false
% 12.06/1.98  --bmc1_ucm                              false
% 12.06/1.98  --bmc1_add_unsat_core                   none
% 12.06/1.98  --bmc1_unsat_core_children              false
% 12.06/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 12.06/1.98  --bmc1_out_stat                         full
% 12.06/1.98  --bmc1_ground_init                      false
% 12.06/1.98  --bmc1_pre_inst_next_state              false
% 12.06/1.98  --bmc1_pre_inst_state                   false
% 12.06/1.98  --bmc1_pre_inst_reach_state             false
% 12.06/1.98  --bmc1_out_unsat_core                   false
% 12.06/1.98  --bmc1_aig_witness_out                  false
% 12.06/1.98  --bmc1_verbose                          false
% 12.06/1.98  --bmc1_dump_clauses_tptp                false
% 12.06/1.98  --bmc1_dump_unsat_core_tptp             false
% 12.06/1.98  --bmc1_dump_file                        -
% 12.06/1.98  --bmc1_ucm_expand_uc_limit              128
% 12.06/1.98  --bmc1_ucm_n_expand_iterations          6
% 12.06/1.98  --bmc1_ucm_extend_mode                  1
% 12.06/1.98  --bmc1_ucm_init_mode                    2
% 12.06/1.98  --bmc1_ucm_cone_mode                    none
% 12.06/1.98  --bmc1_ucm_reduced_relation_type        0
% 12.06/1.98  --bmc1_ucm_relax_model                  4
% 12.06/1.98  --bmc1_ucm_full_tr_after_sat            true
% 12.06/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 12.06/1.98  --bmc1_ucm_layered_model                none
% 12.06/1.98  --bmc1_ucm_max_lemma_size               10
% 12.06/1.98  
% 12.06/1.98  ------ AIG Options
% 12.06/1.98  
% 12.06/1.98  --aig_mode                              false
% 12.06/1.98  
% 12.06/1.98  ------ Instantiation Options
% 12.06/1.98  
% 12.06/1.98  --instantiation_flag                    true
% 12.06/1.98  --inst_sos_flag                         false
% 12.06/1.98  --inst_sos_phase                        true
% 12.06/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.06/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.06/1.98  --inst_lit_sel_side                     num_symb
% 12.06/1.98  --inst_solver_per_active                1400
% 12.06/1.98  --inst_solver_calls_frac                1.
% 12.06/1.98  --inst_passive_queue_type               priority_queues
% 12.06/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.06/1.98  --inst_passive_queues_freq              [25;2]
% 12.06/1.98  --inst_dismatching                      true
% 12.06/1.98  --inst_eager_unprocessed_to_passive     true
% 12.06/1.98  --inst_prop_sim_given                   true
% 12.06/1.98  --inst_prop_sim_new                     false
% 12.06/1.98  --inst_subs_new                         false
% 12.06/1.98  --inst_eq_res_simp                      false
% 12.06/1.98  --inst_subs_given                       false
% 12.06/1.98  --inst_orphan_elimination               true
% 12.06/1.98  --inst_learning_loop_flag               true
% 12.06/1.98  --inst_learning_start                   3000
% 12.06/1.98  --inst_learning_factor                  2
% 12.06/1.98  --inst_start_prop_sim_after_learn       3
% 12.06/1.98  --inst_sel_renew                        solver
% 12.06/1.98  --inst_lit_activity_flag                true
% 12.06/1.98  --inst_restr_to_given                   false
% 12.06/1.98  --inst_activity_threshold               500
% 12.06/1.98  --inst_out_proof                        true
% 12.06/1.98  
% 12.06/1.98  ------ Resolution Options
% 12.06/1.98  
% 12.06/1.98  --resolution_flag                       true
% 12.06/1.98  --res_lit_sel                           adaptive
% 12.06/1.98  --res_lit_sel_side                      none
% 12.06/1.98  --res_ordering                          kbo
% 12.06/1.98  --res_to_prop_solver                    active
% 12.06/1.98  --res_prop_simpl_new                    false
% 12.06/1.98  --res_prop_simpl_given                  true
% 12.06/1.98  --res_passive_queue_type                priority_queues
% 12.06/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.06/1.98  --res_passive_queues_freq               [15;5]
% 12.06/1.98  --res_forward_subs                      full
% 12.06/1.98  --res_backward_subs                     full
% 12.06/1.98  --res_forward_subs_resolution           true
% 12.06/1.98  --res_backward_subs_resolution          true
% 12.06/1.98  --res_orphan_elimination                true
% 12.06/1.98  --res_time_limit                        2.
% 12.06/1.98  --res_out_proof                         true
% 12.06/1.98  
% 12.06/1.98  ------ Superposition Options
% 12.06/1.98  
% 12.06/1.98  --superposition_flag                    true
% 12.06/1.98  --sup_passive_queue_type                priority_queues
% 12.06/1.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.06/1.98  --sup_passive_queues_freq               [1;4]
% 12.06/1.98  --demod_completeness_check              fast
% 12.06/1.98  --demod_use_ground                      true
% 12.06/1.98  --sup_to_prop_solver                    passive
% 12.06/1.98  --sup_prop_simpl_new                    true
% 12.06/1.98  --sup_prop_simpl_given                  true
% 12.06/1.98  --sup_fun_splitting                     false
% 12.06/1.98  --sup_smt_interval                      50000
% 12.06/1.98  
% 12.06/1.98  ------ Superposition Simplification Setup
% 12.06/1.98  
% 12.06/1.98  --sup_indices_passive                   []
% 12.06/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.06/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.06/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.06/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 12.06/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.06/1.98  --sup_full_bw                           [BwDemod]
% 12.06/1.98  --sup_immed_triv                        [TrivRules]
% 12.06/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.06/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.06/1.98  --sup_immed_bw_main                     []
% 12.06/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.06/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 12.06/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.06/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.06/1.98  
% 12.06/1.98  ------ Combination Options
% 12.06/1.98  
% 12.06/1.98  --comb_res_mult                         3
% 12.06/1.98  --comb_sup_mult                         2
% 12.06/1.98  --comb_inst_mult                        10
% 12.06/1.98  
% 12.06/1.98  ------ Debug Options
% 12.06/1.98  
% 12.06/1.98  --dbg_backtrace                         false
% 12.06/1.98  --dbg_dump_prop_clauses                 false
% 12.06/1.98  --dbg_dump_prop_clauses_file            -
% 12.06/1.98  --dbg_out_stat                          false
% 12.06/1.98  
% 12.06/1.98  
% 12.06/1.98  
% 12.06/1.98  
% 12.06/1.98  ------ Proving...
% 12.06/1.98  
% 12.06/1.98  
% 12.06/1.98  % SZS status Theorem for theBenchmark.p
% 12.06/1.98  
% 12.06/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 12.06/1.98  
% 12.06/1.98  fof(f2,axiom,(
% 12.06/1.98    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 12.06/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.06/1.98  
% 12.06/1.98  fof(f39,plain,(
% 12.06/1.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.06/1.98    inference(nnf_transformation,[],[f2])).
% 12.06/1.98  
% 12.06/1.98  fof(f40,plain,(
% 12.06/1.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.06/1.98    inference(flattening,[],[f39])).
% 12.06/1.98  
% 12.06/1.98  fof(f41,plain,(
% 12.06/1.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.06/1.98    inference(rectify,[],[f40])).
% 12.06/1.98  
% 12.06/1.98  fof(f42,plain,(
% 12.06/1.98    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 12.06/1.98    introduced(choice_axiom,[])).
% 12.06/1.98  
% 12.06/1.98  fof(f43,plain,(
% 12.06/1.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.06/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 12.06/1.98  
% 12.06/1.98  fof(f51,plain,(
% 12.06/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 12.06/1.98    inference(cnf_transformation,[],[f43])).
% 12.06/1.98  
% 12.06/1.98  fof(f85,plain,(
% 12.06/1.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 12.06/1.98    inference(equality_resolution,[],[f51])).
% 12.06/1.98  
% 12.06/1.98  fof(f16,axiom,(
% 12.06/1.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 12.06/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.06/1.98  
% 12.06/1.98  fof(f29,plain,(
% 12.06/1.98    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 12.06/1.98    inference(ennf_transformation,[],[f16])).
% 12.06/1.98  
% 12.06/1.98  fof(f30,plain,(
% 12.06/1.98    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 12.06/1.98    inference(flattening,[],[f29])).
% 12.06/1.98  
% 12.06/1.98  fof(f72,plain,(
% 12.06/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 12.06/1.98    inference(cnf_transformation,[],[f30])).
% 12.06/1.98  
% 12.06/1.98  fof(f7,axiom,(
% 12.06/1.98    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 12.06/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.06/1.98  
% 12.06/1.98  fof(f63,plain,(
% 12.06/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 12.06/1.98    inference(cnf_transformation,[],[f7])).
% 12.06/1.98  
% 12.06/1.98  fof(f82,plain,(
% 12.06/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 12.06/1.98    inference(definition_unfolding,[],[f72,f63])).
% 12.06/1.98  
% 12.06/1.98  fof(f1,axiom,(
% 12.06/1.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 12.06/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.06/1.98  
% 12.06/1.98  fof(f20,plain,(
% 12.06/1.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 12.06/1.98    inference(ennf_transformation,[],[f1])).
% 12.06/1.98  
% 12.06/1.98  fof(f35,plain,(
% 12.06/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 12.06/1.98    inference(nnf_transformation,[],[f20])).
% 12.06/1.98  
% 12.06/1.98  fof(f36,plain,(
% 12.06/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.06/1.98    inference(rectify,[],[f35])).
% 12.06/1.98  
% 12.06/1.98  fof(f37,plain,(
% 12.06/1.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 12.06/1.98    introduced(choice_axiom,[])).
% 12.06/1.98  
% 12.06/1.98  fof(f38,plain,(
% 12.06/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.06/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 12.06/1.98  
% 12.06/1.98  fof(f50,plain,(
% 12.06/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 12.06/1.98    inference(cnf_transformation,[],[f38])).
% 12.06/1.98  
% 12.06/1.98  fof(f49,plain,(
% 12.06/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 12.06/1.98    inference(cnf_transformation,[],[f38])).
% 12.06/1.98  
% 12.06/1.98  fof(f12,axiom,(
% 12.06/1.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 12.06/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.06/1.98  
% 12.06/1.98  fof(f23,plain,(
% 12.06/1.98    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 12.06/1.98    inference(ennf_transformation,[],[f12])).
% 12.06/1.98  
% 12.06/1.98  fof(f68,plain,(
% 12.06/1.98    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 12.06/1.98    inference(cnf_transformation,[],[f23])).
% 12.06/1.98  
% 12.06/1.98  fof(f17,axiom,(
% 12.06/1.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 12.06/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.06/1.98  
% 12.06/1.98  fof(f31,plain,(
% 12.06/1.98    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 12.06/1.98    inference(ennf_transformation,[],[f17])).
% 12.06/1.98  
% 12.06/1.98  fof(f32,plain,(
% 12.06/1.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 12.06/1.98    inference(flattening,[],[f31])).
% 12.06/1.98  
% 12.06/1.98  fof(f73,plain,(
% 12.06/1.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 12.06/1.98    inference(cnf_transformation,[],[f32])).
% 12.06/1.98  
% 12.06/1.98  fof(f14,axiom,(
% 12.06/1.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 12.06/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.06/1.98  
% 12.06/1.98  fof(f25,plain,(
% 12.06/1.98    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 12.06/1.98    inference(ennf_transformation,[],[f14])).
% 12.06/1.98  
% 12.06/1.98  fof(f26,plain,(
% 12.06/1.98    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 12.06/1.98    inference(flattening,[],[f25])).
% 12.06/1.98  
% 12.06/1.98  fof(f70,plain,(
% 12.06/1.98    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 12.06/1.98    inference(cnf_transformation,[],[f26])).
% 12.06/1.98  
% 12.06/1.98  fof(f3,axiom,(
% 12.06/1.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 12.06/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.06/1.98  
% 12.06/1.98  fof(f44,plain,(
% 12.06/1.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.06/1.98    inference(nnf_transformation,[],[f3])).
% 12.06/1.98  
% 12.06/1.98  fof(f45,plain,(
% 12.06/1.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.06/1.98    inference(flattening,[],[f44])).
% 12.06/1.98  
% 12.06/1.98  fof(f59,plain,(
% 12.06/1.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 12.06/1.98    inference(cnf_transformation,[],[f45])).
% 12.06/1.98  
% 12.06/1.98  fof(f18,conjecture,(
% 12.06/1.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 12.06/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.06/1.98  
% 12.06/1.98  fof(f19,negated_conjecture,(
% 12.06/1.98    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 12.06/1.98    inference(negated_conjecture,[],[f18])).
% 12.06/1.98  
% 12.06/1.98  fof(f33,plain,(
% 12.06/1.98    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 12.06/1.98    inference(ennf_transformation,[],[f19])).
% 12.06/1.98  
% 12.06/1.98  fof(f34,plain,(
% 12.06/1.98    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 12.06/1.98    inference(flattening,[],[f33])).
% 12.06/1.98  
% 12.06/1.98  fof(f46,plain,(
% 12.06/1.98    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k10_relat_1(sK3,k9_relat_1(sK3,sK2)) != sK2 & v2_funct_1(sK3) & r1_tarski(sK2,k1_relat_1(sK3)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 12.06/1.98    introduced(choice_axiom,[])).
% 12.06/1.98  
% 12.06/1.98  fof(f47,plain,(
% 12.06/1.98    k10_relat_1(sK3,k9_relat_1(sK3,sK2)) != sK2 & v2_funct_1(sK3) & r1_tarski(sK2,k1_relat_1(sK3)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 12.06/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f46])).
% 12.06/1.98  
% 12.06/1.98  fof(f78,plain,(
% 12.06/1.98    k10_relat_1(sK3,k9_relat_1(sK3,sK2)) != sK2),
% 12.06/1.98    inference(cnf_transformation,[],[f47])).
% 12.06/1.98  
% 12.06/1.98  fof(f77,plain,(
% 12.06/1.98    v2_funct_1(sK3)),
% 12.06/1.98    inference(cnf_transformation,[],[f47])).
% 12.06/1.98  
% 12.06/1.98  fof(f76,plain,(
% 12.06/1.98    r1_tarski(sK2,k1_relat_1(sK3))),
% 12.06/1.98    inference(cnf_transformation,[],[f47])).
% 12.06/1.98  
% 12.06/1.98  fof(f75,plain,(
% 12.06/1.98    v1_funct_1(sK3)),
% 12.06/1.98    inference(cnf_transformation,[],[f47])).
% 12.06/1.98  
% 12.06/1.98  fof(f74,plain,(
% 12.06/1.98    v1_relat_1(sK3)),
% 12.06/1.98    inference(cnf_transformation,[],[f47])).
% 12.06/1.98  
% 12.06/1.98  cnf(c_8,plain,
% 12.06/1.98      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 12.06/1.98      inference(cnf_transformation,[],[f85]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_5435,plain,
% 12.06/1.98      ( r2_hidden(sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)),X1)
% 12.06/1.98      | ~ r2_hidden(sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)),k4_xboole_0(X1,X2)) ),
% 12.06/1.98      inference(instantiation,[status(thm)],[c_8]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_43885,plain,
% 12.06/1.98      ( r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,sK2))
% 12.06/1.98      | ~ r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k4_xboole_0(k9_relat_1(sK3,sK2),k4_xboole_0(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3))))) ),
% 12.06/1.98      inference(instantiation,[status(thm)],[c_5435]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_20,plain,
% 12.06/1.98      ( ~ v1_funct_1(X0)
% 12.06/1.98      | ~ v1_relat_1(X0)
% 12.06/1.98      | k4_xboole_0(X1,k4_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 12.06/1.98      inference(cnf_transformation,[],[f82]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_17477,plain,
% 12.06/1.98      ( ~ v1_funct_1(sK3)
% 12.06/1.98      | ~ v1_relat_1(sK3)
% 12.06/1.98      | k4_xboole_0(k9_relat_1(sK3,sK2),k4_xboole_0(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3)))) = k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) ),
% 12.06/1.98      inference(instantiation,[status(thm)],[c_20]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_347,plain,
% 12.06/1.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 12.06/1.98      theory(equality) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_2126,plain,
% 12.06/1.98      ( r2_hidden(X0,X1)
% 12.06/1.98      | ~ r2_hidden(sK0(k9_relat_1(X2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X2,sK2)),k9_relat_1(X2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
% 12.06/1.98      | X1 != k9_relat_1(X2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
% 12.06/1.98      | X0 != sK0(k9_relat_1(X2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X2,sK2)) ),
% 12.06/1.98      inference(instantiation,[status(thm)],[c_347]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_5774,plain,
% 12.06/1.98      ( r2_hidden(sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)),X1)
% 12.06/1.98      | ~ r2_hidden(sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)),k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
% 12.06/1.98      | X1 != k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
% 12.06/1.98      | sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)) != sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)) ),
% 12.06/1.98      inference(instantiation,[status(thm)],[c_2126]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_17476,plain,
% 12.06/1.98      ( ~ r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
% 12.06/1.98      | r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k4_xboole_0(k9_relat_1(sK3,sK2),k4_xboole_0(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3)))))
% 12.06/1.98      | k4_xboole_0(k9_relat_1(sK3,sK2),k4_xboole_0(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3)))) != k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
% 12.06/1.98      | sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) != sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
% 12.06/1.98      inference(instantiation,[status(thm)],[c_5774]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_344,plain,( X0 = X0 ),theory(equality) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_5775,plain,
% 12.06/1.98      ( sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)) = sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)) ),
% 12.06/1.98      inference(instantiation,[status(thm)],[c_344]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_5780,plain,
% 12.06/1.98      ( sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) = sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
% 12.06/1.98      inference(instantiation,[status(thm)],[c_5775]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_0,plain,
% 12.06/1.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 12.06/1.98      inference(cnf_transformation,[],[f50]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_5409,plain,
% 12.06/1.98      ( ~ r2_hidden(sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)),k9_relat_1(X0,sK2))
% 12.06/1.98      | r1_tarski(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)) ),
% 12.06/1.98      inference(instantiation,[status(thm)],[c_0]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_5415,plain,
% 12.06/1.98      ( ~ r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,sK2))
% 12.06/1.98      | r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
% 12.06/1.98      inference(instantiation,[status(thm)],[c_5409]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_1,plain,
% 12.06/1.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 12.06/1.98      inference(cnf_transformation,[],[f49]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_1102,plain,
% 12.06/1.98      ( r2_hidden(sK0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)),k9_relat_1(X0,X1))
% 12.06/1.98      | r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) ),
% 12.06/1.98      inference(instantiation,[status(thm)],[c_1]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_1824,plain,
% 12.06/1.98      ( r2_hidden(sK0(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)),k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
% 12.06/1.98      | r1_tarski(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2)) ),
% 12.06/1.98      inference(instantiation,[status(thm)],[c_1102]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_1826,plain,
% 12.06/1.98      ( r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
% 12.06/1.98      | r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
% 12.06/1.98      inference(instantiation,[status(thm)],[c_1824]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_16,plain,
% 12.06/1.98      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 12.06/1.98      inference(cnf_transformation,[],[f68]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_1432,plain,
% 12.06/1.98      ( r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),k1_relat_1(sK3))
% 12.06/1.98      | ~ v1_relat_1(sK3) ),
% 12.06/1.98      inference(instantiation,[status(thm)],[c_16]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_21,plain,
% 12.06/1.98      ( r1_tarski(X0,X1)
% 12.06/1.98      | ~ r1_tarski(X0,k1_relat_1(X2))
% 12.06/1.98      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 12.06/1.98      | ~ v2_funct_1(X2)
% 12.06/1.98      | ~ v1_funct_1(X2)
% 12.06/1.98      | ~ v1_relat_1(X2) ),
% 12.06/1.98      inference(cnf_transformation,[],[f73]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_1320,plain,
% 12.06/1.98      ( ~ r1_tarski(k9_relat_1(X0,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(X0,sK2))
% 12.06/1.98      | ~ r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),k1_relat_1(X0))
% 12.06/1.98      | r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),sK2)
% 12.06/1.98      | ~ v2_funct_1(X0)
% 12.06/1.98      | ~ v1_funct_1(X0)
% 12.06/1.98      | ~ v1_relat_1(X0) ),
% 12.06/1.98      inference(instantiation,[status(thm)],[c_21]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_1322,plain,
% 12.06/1.98      ( ~ r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2))
% 12.06/1.98      | ~ r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),k1_relat_1(sK3))
% 12.06/1.98      | r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),sK2)
% 12.06/1.98      | ~ v2_funct_1(sK3)
% 12.06/1.98      | ~ v1_funct_1(sK3)
% 12.06/1.98      | ~ v1_relat_1(sK3) ),
% 12.06/1.98      inference(instantiation,[status(thm)],[c_1320]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_18,plain,
% 12.06/1.98      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 12.06/1.98      | ~ r1_tarski(X0,k1_relat_1(X1))
% 12.06/1.98      | ~ v1_relat_1(X1) ),
% 12.06/1.98      inference(cnf_transformation,[],[f70]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_1036,plain,
% 12.06/1.98      ( r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
% 12.06/1.98      | ~ r1_tarski(sK2,k1_relat_1(sK3))
% 12.06/1.98      | ~ v1_relat_1(sK3) ),
% 12.06/1.98      inference(instantiation,[status(thm)],[c_18]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_9,plain,
% 12.06/1.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 12.06/1.98      inference(cnf_transformation,[],[f59]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_990,plain,
% 12.06/1.98      ( ~ r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),sK2)
% 12.06/1.98      | ~ r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
% 12.06/1.98      | k10_relat_1(sK3,k9_relat_1(sK3,sK2)) = sK2 ),
% 12.06/1.98      inference(instantiation,[status(thm)],[c_9]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_22,negated_conjecture,
% 12.06/1.98      ( k10_relat_1(sK3,k9_relat_1(sK3,sK2)) != sK2 ),
% 12.06/1.98      inference(cnf_transformation,[],[f78]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_23,negated_conjecture,
% 12.06/1.98      ( v2_funct_1(sK3) ),
% 12.06/1.98      inference(cnf_transformation,[],[f77]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_24,negated_conjecture,
% 12.06/1.98      ( r1_tarski(sK2,k1_relat_1(sK3)) ),
% 12.06/1.98      inference(cnf_transformation,[],[f76]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_25,negated_conjecture,
% 12.06/1.98      ( v1_funct_1(sK3) ),
% 12.06/1.98      inference(cnf_transformation,[],[f75]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(c_26,negated_conjecture,
% 12.06/1.98      ( v1_relat_1(sK3) ),
% 12.06/1.98      inference(cnf_transformation,[],[f74]) ).
% 12.06/1.98  
% 12.06/1.98  cnf(contradiction,plain,
% 12.06/1.98      ( $false ),
% 12.06/1.98      inference(minisat,
% 12.06/1.98                [status(thm)],
% 12.06/1.98                [c_43885,c_17477,c_17476,c_5780,c_5415,c_1826,c_1432,
% 12.06/1.98                 c_1322,c_1036,c_990,c_22,c_23,c_24,c_25,c_26]) ).
% 12.06/1.98  
% 12.06/1.98  
% 12.06/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 12.06/1.98  
% 12.06/1.98  ------                               Statistics
% 12.06/1.98  
% 12.06/1.98  ------ Selected
% 12.06/1.98  
% 12.06/1.98  total_time:                             1.421
% 12.06/1.98  
%------------------------------------------------------------------------------

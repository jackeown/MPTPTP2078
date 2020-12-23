%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:36 EST 2020

% Result     : Theorem 7.55s
% Output     : CNFRefutation 7.55s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 159 expanded)
%              Number of clauses        :   40 (  44 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  327 ( 647 expanded)
%              Number of equality atoms :   57 ( 117 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
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

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
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

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f60,f75])).

fof(f105,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f98])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f91,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f72,f75,f75])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f84,f91])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f41,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f42,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f54,plain,
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

fof(f55,plain,
    ( k10_relat_1(sK3,k9_relat_1(sK3,sK2)) != sK2
    & v2_funct_1(sK3)
    & r1_tarski(sK2,k1_relat_1(sK3))
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f54])).

fof(f87,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f89,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f90,plain,(
    k10_relat_1(sK3,k9_relat_1(sK3,sK2)) != sK2 ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1908,plain,
    ( r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),X0)
    | ~ r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k6_subset_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_23075,plain,
    ( r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,sK2))
    | ~ r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k6_subset_1(k9_relat_1(sK3,sK2),k6_subset_1(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3))))) ),
    inference(instantiation,[status(thm)],[c_1908])).

cnf(c_25,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_subset_1(X1,k6_subset_1(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_327,plain,
    ( ~ v1_relat_1(X0)
    | k6_subset_1(X1,k6_subset_1(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_30])).

cnf(c_328,plain,
    ( ~ v1_relat_1(sK3)
    | k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(sK3,k1_relat_1(sK3)))) = k9_relat_1(sK3,k10_relat_1(sK3,X0)) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_31,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_332,plain,
    ( k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(sK3,k1_relat_1(sK3)))) = k9_relat_1(sK3,k10_relat_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_328,c_31])).

cnf(c_18940,plain,
    ( k6_subset_1(k9_relat_1(sK3,sK2),k6_subset_1(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3)))) = k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_552,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1373,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
    | X1 != k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
    | X0 != sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_552])).

cnf(c_2734,plain,
    ( r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),X0)
    | ~ r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
    | X0 != k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
    | sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) != sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_1373])).

cnf(c_18939,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
    | r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k6_subset_1(k9_relat_1(sK3,sK2),k6_subset_1(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3)))))
    | sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) != sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2))
    | k6_subset_1(k9_relat_1(sK3,sK2),k6_subset_1(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3)))) != k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_2734])).

cnf(c_548,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2735,plain,
    ( sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) = sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_548])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1886,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,sK2))
    | r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1023,plain,
    ( r2_hidden(sK0(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1)),k9_relat_1(sK3,X0))
    | r1_tarski(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1251,plain,
    ( r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
    | r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_19,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_381,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_31])).

cnf(c_382,plain,
    ( r1_tarski(k10_relat_1(sK3,X0),k1_relat_1(sK3)) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_1205,plain,
    ( r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_382])).

cnf(c_26,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_305,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_28])).

cnf(c_306,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ r1_tarski(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_308,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ r1_tarski(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_306,c_31,c_30])).

cnf(c_1147,plain,
    ( ~ r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),k1_relat_1(sK3))
    | r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),sK2)
    | ~ r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_308])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1032,plain,
    ( ~ r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),sK2)
    | ~ r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
    | k10_relat_1(sK3,k9_relat_1(sK3,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_23,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_395,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_396,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,k9_relat_1(sK3,X0)))
    | ~ r1_tarski(X0,k1_relat_1(sK3)) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_964,plain,
    ( r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
    | ~ r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_27,negated_conjecture,
    ( k10_relat_1(sK3,k9_relat_1(sK3,sK2)) != sK2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_29,negated_conjecture,
    ( r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f88])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23075,c_18940,c_18939,c_2735,c_1886,c_1251,c_1205,c_1147,c_1032,c_964,c_27,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:08:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.55/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.55/1.48  
% 7.55/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.55/1.48  
% 7.55/1.48  ------  iProver source info
% 7.55/1.48  
% 7.55/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.55/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.55/1.48  git: non_committed_changes: false
% 7.55/1.48  git: last_make_outside_of_git: false
% 7.55/1.48  
% 7.55/1.48  ------ 
% 7.55/1.48  ------ Parsing...
% 7.55/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.55/1.48  
% 7.55/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.55/1.48  
% 7.55/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.55/1.48  
% 7.55/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.55/1.48  ------ Proving...
% 7.55/1.48  ------ Problem Properties 
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  clauses                                 28
% 7.55/1.48  conjectures                             2
% 7.55/1.48  EPR                                     5
% 7.55/1.48  Horn                                    23
% 7.55/1.48  unary                                   14
% 7.55/1.48  binary                                  7
% 7.55/1.48  lits                                    50
% 7.55/1.48  lits eq                                 15
% 7.55/1.48  fd_pure                                 0
% 7.55/1.48  fd_pseudo                               0
% 7.55/1.48  fd_cond                                 1
% 7.55/1.48  fd_pseudo_cond                          4
% 7.55/1.48  AC symbols                              0
% 7.55/1.48  
% 7.55/1.48  ------ Input Options Time Limit: Unbounded
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  ------ 
% 7.55/1.48  Current options:
% 7.55/1.48  ------ 
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  ------ Proving...
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  % SZS status Theorem for theBenchmark.p
% 7.55/1.48  
% 7.55/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.55/1.48  
% 7.55/1.48  fof(f3,axiom,(
% 7.55/1.48    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f47,plain,(
% 7.55/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.55/1.48    inference(nnf_transformation,[],[f3])).
% 7.55/1.48  
% 7.55/1.48  fof(f48,plain,(
% 7.55/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.55/1.48    inference(flattening,[],[f47])).
% 7.55/1.48  
% 7.55/1.48  fof(f49,plain,(
% 7.55/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.55/1.48    inference(rectify,[],[f48])).
% 7.55/1.48  
% 7.55/1.48  fof(f50,plain,(
% 7.55/1.48    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.55/1.48    introduced(choice_axiom,[])).
% 7.55/1.48  
% 7.55/1.48  fof(f51,plain,(
% 7.55/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.55/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).
% 7.55/1.48  
% 7.55/1.48  fof(f60,plain,(
% 7.55/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.55/1.48    inference(cnf_transformation,[],[f51])).
% 7.55/1.48  
% 7.55/1.48  fof(f11,axiom,(
% 7.55/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f75,plain,(
% 7.55/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f11])).
% 7.55/1.48  
% 7.55/1.48  fof(f98,plain,(
% 7.55/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 7.55/1.48    inference(definition_unfolding,[],[f60,f75])).
% 7.55/1.48  
% 7.55/1.48  fof(f105,plain,(
% 7.55/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 7.55/1.48    inference(equality_resolution,[],[f98])).
% 7.55/1.48  
% 7.55/1.48  fof(f20,axiom,(
% 7.55/1.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f37,plain,(
% 7.55/1.48    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.55/1.48    inference(ennf_transformation,[],[f20])).
% 7.55/1.48  
% 7.55/1.48  fof(f38,plain,(
% 7.55/1.48    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.55/1.48    inference(flattening,[],[f37])).
% 7.55/1.48  
% 7.55/1.48  fof(f84,plain,(
% 7.55/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f38])).
% 7.55/1.48  
% 7.55/1.48  fof(f8,axiom,(
% 7.55/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f72,plain,(
% 7.55/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.55/1.48    inference(cnf_transformation,[],[f8])).
% 7.55/1.48  
% 7.55/1.48  fof(f91,plain,(
% 7.55/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 7.55/1.48    inference(definition_unfolding,[],[f72,f75,f75])).
% 7.55/1.48  
% 7.55/1.48  fof(f102,plain,(
% 7.55/1.48    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.55/1.48    inference(definition_unfolding,[],[f84,f91])).
% 7.55/1.48  
% 7.55/1.48  fof(f22,conjecture,(
% 7.55/1.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f23,negated_conjecture,(
% 7.55/1.48    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 7.55/1.48    inference(negated_conjecture,[],[f22])).
% 7.55/1.48  
% 7.55/1.48  fof(f41,plain,(
% 7.55/1.48    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 7.55/1.48    inference(ennf_transformation,[],[f23])).
% 7.55/1.48  
% 7.55/1.48  fof(f42,plain,(
% 7.55/1.48    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.55/1.48    inference(flattening,[],[f41])).
% 7.55/1.48  
% 7.55/1.48  fof(f54,plain,(
% 7.55/1.48    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k10_relat_1(sK3,k9_relat_1(sK3,sK2)) != sK2 & v2_funct_1(sK3) & r1_tarski(sK2,k1_relat_1(sK3)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 7.55/1.48    introduced(choice_axiom,[])).
% 7.55/1.48  
% 7.55/1.48  fof(f55,plain,(
% 7.55/1.48    k10_relat_1(sK3,k9_relat_1(sK3,sK2)) != sK2 & v2_funct_1(sK3) & r1_tarski(sK2,k1_relat_1(sK3)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 7.55/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f54])).
% 7.55/1.48  
% 7.55/1.48  fof(f87,plain,(
% 7.55/1.48    v1_funct_1(sK3)),
% 7.55/1.48    inference(cnf_transformation,[],[f55])).
% 7.55/1.48  
% 7.55/1.48  fof(f86,plain,(
% 7.55/1.48    v1_relat_1(sK3)),
% 7.55/1.48    inference(cnf_transformation,[],[f55])).
% 7.55/1.48  
% 7.55/1.48  fof(f2,axiom,(
% 7.55/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f24,plain,(
% 7.55/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.55/1.48    inference(ennf_transformation,[],[f2])).
% 7.55/1.48  
% 7.55/1.48  fof(f43,plain,(
% 7.55/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.55/1.48    inference(nnf_transformation,[],[f24])).
% 7.55/1.48  
% 7.55/1.48  fof(f44,plain,(
% 7.55/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.55/1.48    inference(rectify,[],[f43])).
% 7.55/1.48  
% 7.55/1.48  fof(f45,plain,(
% 7.55/1.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.55/1.48    introduced(choice_axiom,[])).
% 7.55/1.48  
% 7.55/1.48  fof(f46,plain,(
% 7.55/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.55/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).
% 7.55/1.48  
% 7.55/1.48  fof(f59,plain,(
% 7.55/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f46])).
% 7.55/1.48  
% 7.55/1.48  fof(f58,plain,(
% 7.55/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f46])).
% 7.55/1.48  
% 7.55/1.48  fof(f14,axiom,(
% 7.55/1.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f27,plain,(
% 7.55/1.48    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.55/1.48    inference(ennf_transformation,[],[f14])).
% 7.55/1.48  
% 7.55/1.48  fof(f78,plain,(
% 7.55/1.48    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f27])).
% 7.55/1.48  
% 7.55/1.48  fof(f21,axiom,(
% 7.55/1.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f39,plain,(
% 7.55/1.48    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.55/1.48    inference(ennf_transformation,[],[f21])).
% 7.55/1.48  
% 7.55/1.48  fof(f40,plain,(
% 7.55/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.55/1.48    inference(flattening,[],[f39])).
% 7.55/1.48  
% 7.55/1.48  fof(f85,plain,(
% 7.55/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f40])).
% 7.55/1.48  
% 7.55/1.48  fof(f89,plain,(
% 7.55/1.48    v2_funct_1(sK3)),
% 7.55/1.48    inference(cnf_transformation,[],[f55])).
% 7.55/1.48  
% 7.55/1.48  fof(f4,axiom,(
% 7.55/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f52,plain,(
% 7.55/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.55/1.48    inference(nnf_transformation,[],[f4])).
% 7.55/1.48  
% 7.55/1.48  fof(f53,plain,(
% 7.55/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.55/1.48    inference(flattening,[],[f52])).
% 7.55/1.48  
% 7.55/1.48  fof(f68,plain,(
% 7.55/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f53])).
% 7.55/1.48  
% 7.55/1.48  fof(f18,axiom,(
% 7.55/1.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f33,plain,(
% 7.55/1.48    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.55/1.48    inference(ennf_transformation,[],[f18])).
% 7.55/1.48  
% 7.55/1.48  fof(f34,plain,(
% 7.55/1.48    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.55/1.48    inference(flattening,[],[f33])).
% 7.55/1.48  
% 7.55/1.48  fof(f82,plain,(
% 7.55/1.48    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f34])).
% 7.55/1.48  
% 7.55/1.48  fof(f90,plain,(
% 7.55/1.48    k10_relat_1(sK3,k9_relat_1(sK3,sK2)) != sK2),
% 7.55/1.48    inference(cnf_transformation,[],[f55])).
% 7.55/1.48  
% 7.55/1.48  fof(f88,plain,(
% 7.55/1.48    r1_tarski(sK2,k1_relat_1(sK3))),
% 7.55/1.48    inference(cnf_transformation,[],[f55])).
% 7.55/1.48  
% 7.55/1.48  cnf(c_9,plain,
% 7.55/1.48      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k6_subset_1(X1,X2)) ),
% 7.55/1.48      inference(cnf_transformation,[],[f105]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1908,plain,
% 7.55/1.48      ( r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),X0)
% 7.55/1.48      | ~ r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k6_subset_1(X0,X1)) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_9]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_23075,plain,
% 7.55/1.48      ( r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,sK2))
% 7.55/1.48      | ~ r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k6_subset_1(k9_relat_1(sK3,sK2),k6_subset_1(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3))))) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_1908]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_25,plain,
% 7.55/1.48      ( ~ v1_funct_1(X0)
% 7.55/1.48      | ~ v1_relat_1(X0)
% 7.55/1.48      | k6_subset_1(X1,k6_subset_1(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 7.55/1.48      inference(cnf_transformation,[],[f102]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_30,negated_conjecture,
% 7.55/1.48      ( v1_funct_1(sK3) ),
% 7.55/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_327,plain,
% 7.55/1.48      ( ~ v1_relat_1(X0)
% 7.55/1.48      | k6_subset_1(X1,k6_subset_1(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1))
% 7.55/1.48      | sK3 != X0 ),
% 7.55/1.48      inference(resolution_lifted,[status(thm)],[c_25,c_30]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_328,plain,
% 7.55/1.48      ( ~ v1_relat_1(sK3)
% 7.55/1.48      | k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(sK3,k1_relat_1(sK3)))) = k9_relat_1(sK3,k10_relat_1(sK3,X0)) ),
% 7.55/1.48      inference(unflattening,[status(thm)],[c_327]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_31,negated_conjecture,
% 7.55/1.48      ( v1_relat_1(sK3) ),
% 7.55/1.48      inference(cnf_transformation,[],[f86]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_332,plain,
% 7.55/1.48      ( k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(sK3,k1_relat_1(sK3)))) = k9_relat_1(sK3,k10_relat_1(sK3,X0)) ),
% 7.55/1.48      inference(global_propositional_subsumption,
% 7.55/1.48                [status(thm)],
% 7.55/1.48                [c_328,c_31]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_18940,plain,
% 7.55/1.48      ( k6_subset_1(k9_relat_1(sK3,sK2),k6_subset_1(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3)))) = k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_332]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_552,plain,
% 7.55/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.55/1.48      theory(equality) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1373,plain,
% 7.55/1.48      ( r2_hidden(X0,X1)
% 7.55/1.48      | ~ r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
% 7.55/1.48      | X1 != k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
% 7.55/1.48      | X0 != sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_552]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_2734,plain,
% 7.55/1.48      ( r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),X0)
% 7.55/1.48      | ~ r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
% 7.55/1.48      | X0 != k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
% 7.55/1.48      | sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) != sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_1373]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_18939,plain,
% 7.55/1.48      ( ~ r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
% 7.55/1.48      | r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k6_subset_1(k9_relat_1(sK3,sK2),k6_subset_1(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3)))))
% 7.55/1.48      | sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) != sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2))
% 7.55/1.48      | k6_subset_1(k9_relat_1(sK3,sK2),k6_subset_1(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3)))) != k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_2734]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_548,plain,( X0 = X0 ),theory(equality) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_2735,plain,
% 7.55/1.48      ( sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) = sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_548]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1,plain,
% 7.55/1.48      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.55/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1886,plain,
% 7.55/1.48      ( ~ r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,sK2))
% 7.55/1.48      | r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_2,plain,
% 7.55/1.48      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.55/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1023,plain,
% 7.55/1.48      ( r2_hidden(sK0(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1)),k9_relat_1(sK3,X0))
% 7.55/1.48      | r1_tarski(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1)) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1251,plain,
% 7.55/1.48      ( r2_hidden(sK0(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)),k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
% 7.55/1.48      | r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_1023]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_19,plain,
% 7.55/1.48      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.55/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_381,plain,
% 7.55/1.48      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | sK3 != X0 ),
% 7.55/1.48      inference(resolution_lifted,[status(thm)],[c_19,c_31]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_382,plain,
% 7.55/1.48      ( r1_tarski(k10_relat_1(sK3,X0),k1_relat_1(sK3)) ),
% 7.55/1.48      inference(unflattening,[status(thm)],[c_381]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1205,plain,
% 7.55/1.48      ( r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),k1_relat_1(sK3)) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_382]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_26,plain,
% 7.55/1.48      ( r1_tarski(X0,X1)
% 7.55/1.48      | ~ r1_tarski(X0,k1_relat_1(X2))
% 7.55/1.48      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 7.55/1.48      | ~ v1_funct_1(X2)
% 7.55/1.48      | ~ v2_funct_1(X2)
% 7.55/1.48      | ~ v1_relat_1(X2) ),
% 7.55/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_28,negated_conjecture,
% 7.55/1.48      ( v2_funct_1(sK3) ),
% 7.55/1.48      inference(cnf_transformation,[],[f89]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_305,plain,
% 7.55/1.48      ( r1_tarski(X0,X1)
% 7.55/1.48      | ~ r1_tarski(X0,k1_relat_1(X2))
% 7.55/1.48      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 7.55/1.48      | ~ v1_funct_1(X2)
% 7.55/1.48      | ~ v1_relat_1(X2)
% 7.55/1.48      | sK3 != X2 ),
% 7.55/1.48      inference(resolution_lifted,[status(thm)],[c_26,c_28]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_306,plain,
% 7.55/1.48      ( r1_tarski(X0,X1)
% 7.55/1.48      | ~ r1_tarski(X0,k1_relat_1(sK3))
% 7.55/1.48      | ~ r1_tarski(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1))
% 7.55/1.48      | ~ v1_funct_1(sK3)
% 7.55/1.48      | ~ v1_relat_1(sK3) ),
% 7.55/1.48      inference(unflattening,[status(thm)],[c_305]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_308,plain,
% 7.55/1.48      ( r1_tarski(X0,X1)
% 7.55/1.48      | ~ r1_tarski(X0,k1_relat_1(sK3))
% 7.55/1.48      | ~ r1_tarski(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1)) ),
% 7.55/1.48      inference(global_propositional_subsumption,
% 7.55/1.48                [status(thm)],
% 7.55/1.48                [c_306,c_31,c_30]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1147,plain,
% 7.55/1.48      ( ~ r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),k1_relat_1(sK3))
% 7.55/1.48      | r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),sK2)
% 7.55/1.48      | ~ r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,sK2))),k9_relat_1(sK3,sK2)) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_308]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_10,plain,
% 7.55/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.55/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1032,plain,
% 7.55/1.48      ( ~ r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK2)),sK2)
% 7.55/1.48      | ~ r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
% 7.55/1.48      | k10_relat_1(sK3,k9_relat_1(sK3,sK2)) = sK2 ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_10]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_23,plain,
% 7.55/1.48      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 7.55/1.48      | ~ r1_tarski(X0,k1_relat_1(X1))
% 7.55/1.48      | ~ v1_relat_1(X1) ),
% 7.55/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_395,plain,
% 7.55/1.48      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 7.55/1.48      | ~ r1_tarski(X0,k1_relat_1(X1))
% 7.55/1.48      | sK3 != X1 ),
% 7.55/1.48      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_396,plain,
% 7.55/1.48      ( r1_tarski(X0,k10_relat_1(sK3,k9_relat_1(sK3,X0)))
% 7.55/1.48      | ~ r1_tarski(X0,k1_relat_1(sK3)) ),
% 7.55/1.48      inference(unflattening,[status(thm)],[c_395]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_964,plain,
% 7.55/1.48      ( r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
% 7.55/1.48      | ~ r1_tarski(sK2,k1_relat_1(sK3)) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_396]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_27,negated_conjecture,
% 7.55/1.48      ( k10_relat_1(sK3,k9_relat_1(sK3,sK2)) != sK2 ),
% 7.55/1.48      inference(cnf_transformation,[],[f90]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_29,negated_conjecture,
% 7.55/1.48      ( r1_tarski(sK2,k1_relat_1(sK3)) ),
% 7.55/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(contradiction,plain,
% 7.55/1.48      ( $false ),
% 7.55/1.48      inference(minisat,
% 7.55/1.48                [status(thm)],
% 7.55/1.48                [c_23075,c_18940,c_18939,c_2735,c_1886,c_1251,c_1205,
% 7.55/1.48                 c_1147,c_1032,c_964,c_27,c_29]) ).
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.55/1.48  
% 7.55/1.48  ------                               Statistics
% 7.55/1.48  
% 7.55/1.48  ------ Selected
% 7.55/1.48  
% 7.55/1.48  total_time:                             0.594
% 7.55/1.48  
%------------------------------------------------------------------------------

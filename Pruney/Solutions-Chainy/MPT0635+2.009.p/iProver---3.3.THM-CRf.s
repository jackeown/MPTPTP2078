%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:52 EST 2020

% Result     : Theorem 8.03s
% Output     : CNFRefutation 8.03s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 156 expanded)
%              Number of clauses        :   41 (  45 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  337 ( 595 expanded)
%              Number of equality atoms :   58 ( 122 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f49])).

fof(f46,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f31,f38,f38])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
      & r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
    & r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f29])).

fof(f52,plain,(
    r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    r2_hidden(sK1,k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),sK2))) ),
    inference(definition_unfolding,[],[f52,f38])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_122,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_7])).

cnf(c_123,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(renaming,[status(thm)],[c_122])).

cnf(c_1121,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X0),sK3))
    | ~ v1_relat_1(k6_relat_1(X0))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_123])).

cnf(c_14911,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_14,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_5910,plain,
    ( v1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3))
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_990,plain,
    ( r2_hidden(k4_tarski(sK1,X0),k5_relat_1(k6_relat_1(X1),sK3))
    | ~ r2_hidden(k4_tarski(sK1,X0),sK3)
    | ~ r2_hidden(sK1,X1)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4072,plain,
    ( r2_hidden(k4_tarski(sK1,X0),k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ r2_hidden(k4_tarski(sK1,X0),sK3)
    | ~ r2_hidden(sK1,sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_4746,plain,
    ( r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),sK3)
    | ~ r2_hidden(sK1,sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4072])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3063,plain,
    ( r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),sK3)
    | ~ r2_hidden(sK1,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_13,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2191,plain,
    ( v1_funct_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK1,k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),sK2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_560,plain,
    ( r2_hidden(sK1,k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1153,plain,
    ( r2_hidden(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_560])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_572,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1496,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1153,c_572])).

cnf(c_1501,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1496])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_571,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1322,plain,
    ( r2_hidden(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1153,c_571])).

cnf(c_1327,plain,
    ( r2_hidden(sK1,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1322])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v1_funct_1(k5_relat_1(X1,X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1296,plain,
    ( v1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ v1_funct_1(k6_relat_1(sK2))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_16,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_910,plain,
    ( ~ r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ v1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK2),sK3))
    | k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) = k1_funct_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_232,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_725,plain,
    ( k1_funct_1(sK3,sK1) = k1_funct_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_233,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_602,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) != X0
    | k1_funct_1(sK3,sK1) != X0
    | k1_funct_1(sK3,sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_233])).

cnf(c_640,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) != k1_funct_1(sK3,sK1)
    | k1_funct_1(sK3,sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
    | k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_18,negated_conjecture,
    ( k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14911,c_5910,c_4746,c_3063,c_2191,c_1501,c_1327,c_1296,c_910,c_725,c_640,c_18,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:04:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.03/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.03/1.48  
% 8.03/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.03/1.48  
% 8.03/1.48  ------  iProver source info
% 8.03/1.48  
% 8.03/1.48  git: date: 2020-06-30 10:37:57 +0100
% 8.03/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.03/1.48  git: non_committed_changes: false
% 8.03/1.48  git: last_make_outside_of_git: false
% 8.03/1.48  
% 8.03/1.48  ------ 
% 8.03/1.48  
% 8.03/1.48  ------ Input Options
% 8.03/1.48  
% 8.03/1.48  --out_options                           all
% 8.03/1.48  --tptp_safe_out                         true
% 8.03/1.48  --problem_path                          ""
% 8.03/1.48  --include_path                          ""
% 8.03/1.48  --clausifier                            res/vclausify_rel
% 8.03/1.48  --clausifier_options                    ""
% 8.03/1.48  --stdin                                 false
% 8.03/1.48  --stats_out                             all
% 8.03/1.48  
% 8.03/1.48  ------ General Options
% 8.03/1.48  
% 8.03/1.48  --fof                                   false
% 8.03/1.48  --time_out_real                         305.
% 8.03/1.48  --time_out_virtual                      -1.
% 8.03/1.48  --symbol_type_check                     false
% 8.03/1.48  --clausify_out                          false
% 8.03/1.48  --sig_cnt_out                           false
% 8.03/1.48  --trig_cnt_out                          false
% 8.03/1.48  --trig_cnt_out_tolerance                1.
% 8.03/1.48  --trig_cnt_out_sk_spl                   false
% 8.03/1.48  --abstr_cl_out                          false
% 8.03/1.48  
% 8.03/1.48  ------ Global Options
% 8.03/1.48  
% 8.03/1.48  --schedule                              default
% 8.03/1.48  --add_important_lit                     false
% 8.03/1.48  --prop_solver_per_cl                    1000
% 8.03/1.48  --min_unsat_core                        false
% 8.03/1.48  --soft_assumptions                      false
% 8.03/1.48  --soft_lemma_size                       3
% 8.03/1.48  --prop_impl_unit_size                   0
% 8.03/1.48  --prop_impl_unit                        []
% 8.03/1.48  --share_sel_clauses                     true
% 8.03/1.48  --reset_solvers                         false
% 8.03/1.48  --bc_imp_inh                            [conj_cone]
% 8.03/1.48  --conj_cone_tolerance                   3.
% 8.03/1.48  --extra_neg_conj                        none
% 8.03/1.48  --large_theory_mode                     true
% 8.03/1.48  --prolific_symb_bound                   200
% 8.03/1.48  --lt_threshold                          2000
% 8.03/1.48  --clause_weak_htbl                      true
% 8.03/1.48  --gc_record_bc_elim                     false
% 8.03/1.48  
% 8.03/1.48  ------ Preprocessing Options
% 8.03/1.48  
% 8.03/1.48  --preprocessing_flag                    true
% 8.03/1.48  --time_out_prep_mult                    0.1
% 8.03/1.48  --splitting_mode                        input
% 8.03/1.48  --splitting_grd                         true
% 8.03/1.48  --splitting_cvd                         false
% 8.03/1.48  --splitting_cvd_svl                     false
% 8.03/1.48  --splitting_nvd                         32
% 8.03/1.48  --sub_typing                            true
% 8.03/1.48  --prep_gs_sim                           true
% 8.03/1.48  --prep_unflatten                        true
% 8.03/1.48  --prep_res_sim                          true
% 8.03/1.48  --prep_upred                            true
% 8.03/1.48  --prep_sem_filter                       exhaustive
% 8.03/1.48  --prep_sem_filter_out                   false
% 8.03/1.48  --pred_elim                             true
% 8.03/1.48  --res_sim_input                         true
% 8.03/1.48  --eq_ax_congr_red                       true
% 8.03/1.48  --pure_diseq_elim                       true
% 8.03/1.48  --brand_transform                       false
% 8.03/1.48  --non_eq_to_eq                          false
% 8.03/1.48  --prep_def_merge                        true
% 8.03/1.48  --prep_def_merge_prop_impl              false
% 8.03/1.48  --prep_def_merge_mbd                    true
% 8.03/1.48  --prep_def_merge_tr_red                 false
% 8.03/1.48  --prep_def_merge_tr_cl                  false
% 8.03/1.48  --smt_preprocessing                     true
% 8.03/1.48  --smt_ac_axioms                         fast
% 8.03/1.48  --preprocessed_out                      false
% 8.03/1.48  --preprocessed_stats                    false
% 8.03/1.48  
% 8.03/1.48  ------ Abstraction refinement Options
% 8.03/1.48  
% 8.03/1.48  --abstr_ref                             []
% 8.03/1.48  --abstr_ref_prep                        false
% 8.03/1.48  --abstr_ref_until_sat                   false
% 8.03/1.48  --abstr_ref_sig_restrict                funpre
% 8.03/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 8.03/1.48  --abstr_ref_under                       []
% 8.03/1.48  
% 8.03/1.48  ------ SAT Options
% 8.03/1.48  
% 8.03/1.48  --sat_mode                              false
% 8.03/1.48  --sat_fm_restart_options                ""
% 8.03/1.48  --sat_gr_def                            false
% 8.03/1.48  --sat_epr_types                         true
% 8.03/1.48  --sat_non_cyclic_types                  false
% 8.03/1.48  --sat_finite_models                     false
% 8.03/1.48  --sat_fm_lemmas                         false
% 8.03/1.48  --sat_fm_prep                           false
% 8.03/1.48  --sat_fm_uc_incr                        true
% 8.03/1.48  --sat_out_model                         small
% 8.03/1.48  --sat_out_clauses                       false
% 8.03/1.48  
% 8.03/1.48  ------ QBF Options
% 8.03/1.48  
% 8.03/1.48  --qbf_mode                              false
% 8.03/1.48  --qbf_elim_univ                         false
% 8.03/1.48  --qbf_dom_inst                          none
% 8.03/1.48  --qbf_dom_pre_inst                      false
% 8.03/1.48  --qbf_sk_in                             false
% 8.03/1.48  --qbf_pred_elim                         true
% 8.03/1.48  --qbf_split                             512
% 8.03/1.48  
% 8.03/1.48  ------ BMC1 Options
% 8.03/1.48  
% 8.03/1.48  --bmc1_incremental                      false
% 8.03/1.48  --bmc1_axioms                           reachable_all
% 8.03/1.48  --bmc1_min_bound                        0
% 8.03/1.48  --bmc1_max_bound                        -1
% 8.03/1.48  --bmc1_max_bound_default                -1
% 8.03/1.48  --bmc1_symbol_reachability              true
% 8.03/1.48  --bmc1_property_lemmas                  false
% 8.03/1.48  --bmc1_k_induction                      false
% 8.03/1.48  --bmc1_non_equiv_states                 false
% 8.03/1.48  --bmc1_deadlock                         false
% 8.03/1.48  --bmc1_ucm                              false
% 8.03/1.48  --bmc1_add_unsat_core                   none
% 8.03/1.48  --bmc1_unsat_core_children              false
% 8.03/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 8.03/1.48  --bmc1_out_stat                         full
% 8.03/1.48  --bmc1_ground_init                      false
% 8.03/1.48  --bmc1_pre_inst_next_state              false
% 8.03/1.48  --bmc1_pre_inst_state                   false
% 8.03/1.48  --bmc1_pre_inst_reach_state             false
% 8.03/1.48  --bmc1_out_unsat_core                   false
% 8.03/1.48  --bmc1_aig_witness_out                  false
% 8.03/1.48  --bmc1_verbose                          false
% 8.03/1.48  --bmc1_dump_clauses_tptp                false
% 8.03/1.48  --bmc1_dump_unsat_core_tptp             false
% 8.03/1.48  --bmc1_dump_file                        -
% 8.03/1.48  --bmc1_ucm_expand_uc_limit              128
% 8.03/1.48  --bmc1_ucm_n_expand_iterations          6
% 8.03/1.48  --bmc1_ucm_extend_mode                  1
% 8.03/1.48  --bmc1_ucm_init_mode                    2
% 8.03/1.48  --bmc1_ucm_cone_mode                    none
% 8.03/1.48  --bmc1_ucm_reduced_relation_type        0
% 8.03/1.48  --bmc1_ucm_relax_model                  4
% 8.03/1.48  --bmc1_ucm_full_tr_after_sat            true
% 8.03/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 8.03/1.48  --bmc1_ucm_layered_model                none
% 8.03/1.48  --bmc1_ucm_max_lemma_size               10
% 8.03/1.48  
% 8.03/1.48  ------ AIG Options
% 8.03/1.48  
% 8.03/1.48  --aig_mode                              false
% 8.03/1.48  
% 8.03/1.48  ------ Instantiation Options
% 8.03/1.48  
% 8.03/1.48  --instantiation_flag                    true
% 8.03/1.48  --inst_sos_flag                         true
% 8.03/1.48  --inst_sos_phase                        true
% 8.03/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.03/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.03/1.48  --inst_lit_sel_side                     num_symb
% 8.03/1.48  --inst_solver_per_active                1400
% 8.03/1.48  --inst_solver_calls_frac                1.
% 8.03/1.48  --inst_passive_queue_type               priority_queues
% 8.03/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.03/1.48  --inst_passive_queues_freq              [25;2]
% 8.03/1.48  --inst_dismatching                      true
% 8.03/1.48  --inst_eager_unprocessed_to_passive     true
% 8.03/1.48  --inst_prop_sim_given                   true
% 8.03/1.48  --inst_prop_sim_new                     false
% 8.03/1.48  --inst_subs_new                         false
% 8.03/1.48  --inst_eq_res_simp                      false
% 8.03/1.48  --inst_subs_given                       false
% 8.03/1.48  --inst_orphan_elimination               true
% 8.03/1.48  --inst_learning_loop_flag               true
% 8.03/1.48  --inst_learning_start                   3000
% 8.03/1.48  --inst_learning_factor                  2
% 8.03/1.48  --inst_start_prop_sim_after_learn       3
% 8.03/1.48  --inst_sel_renew                        solver
% 8.03/1.48  --inst_lit_activity_flag                true
% 8.03/1.48  --inst_restr_to_given                   false
% 8.03/1.48  --inst_activity_threshold               500
% 8.03/1.48  --inst_out_proof                        true
% 8.03/1.48  
% 8.03/1.48  ------ Resolution Options
% 8.03/1.48  
% 8.03/1.48  --resolution_flag                       true
% 8.03/1.48  --res_lit_sel                           adaptive
% 8.03/1.48  --res_lit_sel_side                      none
% 8.03/1.48  --res_ordering                          kbo
% 8.03/1.48  --res_to_prop_solver                    active
% 8.03/1.48  --res_prop_simpl_new                    false
% 8.03/1.48  --res_prop_simpl_given                  true
% 8.03/1.48  --res_passive_queue_type                priority_queues
% 8.03/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.03/1.48  --res_passive_queues_freq               [15;5]
% 8.03/1.48  --res_forward_subs                      full
% 8.03/1.48  --res_backward_subs                     full
% 8.03/1.48  --res_forward_subs_resolution           true
% 8.03/1.48  --res_backward_subs_resolution          true
% 8.03/1.48  --res_orphan_elimination                true
% 8.03/1.48  --res_time_limit                        2.
% 8.03/1.48  --res_out_proof                         true
% 8.03/1.48  
% 8.03/1.48  ------ Superposition Options
% 8.03/1.48  
% 8.03/1.48  --superposition_flag                    true
% 8.03/1.48  --sup_passive_queue_type                priority_queues
% 8.03/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.03/1.48  --sup_passive_queues_freq               [8;1;4]
% 8.03/1.48  --demod_completeness_check              fast
% 8.03/1.48  --demod_use_ground                      true
% 8.03/1.48  --sup_to_prop_solver                    passive
% 8.03/1.48  --sup_prop_simpl_new                    true
% 8.03/1.48  --sup_prop_simpl_given                  true
% 8.03/1.48  --sup_fun_splitting                     true
% 8.03/1.48  --sup_smt_interval                      50000
% 8.03/1.48  
% 8.03/1.48  ------ Superposition Simplification Setup
% 8.03/1.48  
% 8.03/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.03/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.03/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.03/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.03/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 8.03/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.03/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.03/1.48  --sup_immed_triv                        [TrivRules]
% 8.03/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.48  --sup_immed_bw_main                     []
% 8.03/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.03/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 8.03/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.48  --sup_input_bw                          []
% 8.03/1.48  
% 8.03/1.48  ------ Combination Options
% 8.03/1.48  
% 8.03/1.48  --comb_res_mult                         3
% 8.03/1.48  --comb_sup_mult                         2
% 8.03/1.48  --comb_inst_mult                        10
% 8.03/1.48  
% 8.03/1.48  ------ Debug Options
% 8.03/1.48  
% 8.03/1.48  --dbg_backtrace                         false
% 8.03/1.48  --dbg_dump_prop_clauses                 false
% 8.03/1.48  --dbg_dump_prop_clauses_file            -
% 8.03/1.48  --dbg_out_stat                          false
% 8.03/1.48  ------ Parsing...
% 8.03/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.03/1.48  
% 8.03/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 8.03/1.48  
% 8.03/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.03/1.48  
% 8.03/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.48  ------ Proving...
% 8.03/1.48  ------ Problem Properties 
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  clauses                                 22
% 8.03/1.48  conjectures                             4
% 8.03/1.48  EPR                                     2
% 8.03/1.48  Horn                                    20
% 8.03/1.48  unary                                   7
% 8.03/1.48  binary                                  2
% 8.03/1.48  lits                                    57
% 8.03/1.48  lits eq                                 6
% 8.03/1.48  fd_pure                                 0
% 8.03/1.48  fd_pseudo                               0
% 8.03/1.48  fd_cond                                 0
% 8.03/1.48  fd_pseudo_cond                          4
% 8.03/1.48  AC symbols                              0
% 8.03/1.48  
% 8.03/1.48  ------ Schedule dynamic 5 is on 
% 8.03/1.48  
% 8.03/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  ------ 
% 8.03/1.48  Current options:
% 8.03/1.48  ------ 
% 8.03/1.48  
% 8.03/1.48  ------ Input Options
% 8.03/1.48  
% 8.03/1.48  --out_options                           all
% 8.03/1.48  --tptp_safe_out                         true
% 8.03/1.48  --problem_path                          ""
% 8.03/1.48  --include_path                          ""
% 8.03/1.48  --clausifier                            res/vclausify_rel
% 8.03/1.48  --clausifier_options                    ""
% 8.03/1.48  --stdin                                 false
% 8.03/1.48  --stats_out                             all
% 8.03/1.48  
% 8.03/1.48  ------ General Options
% 8.03/1.48  
% 8.03/1.48  --fof                                   false
% 8.03/1.48  --time_out_real                         305.
% 8.03/1.48  --time_out_virtual                      -1.
% 8.03/1.48  --symbol_type_check                     false
% 8.03/1.48  --clausify_out                          false
% 8.03/1.48  --sig_cnt_out                           false
% 8.03/1.48  --trig_cnt_out                          false
% 8.03/1.48  --trig_cnt_out_tolerance                1.
% 8.03/1.48  --trig_cnt_out_sk_spl                   false
% 8.03/1.48  --abstr_cl_out                          false
% 8.03/1.48  
% 8.03/1.48  ------ Global Options
% 8.03/1.48  
% 8.03/1.48  --schedule                              default
% 8.03/1.48  --add_important_lit                     false
% 8.03/1.48  --prop_solver_per_cl                    1000
% 8.03/1.48  --min_unsat_core                        false
% 8.03/1.48  --soft_assumptions                      false
% 8.03/1.48  --soft_lemma_size                       3
% 8.03/1.48  --prop_impl_unit_size                   0
% 8.03/1.48  --prop_impl_unit                        []
% 8.03/1.48  --share_sel_clauses                     true
% 8.03/1.48  --reset_solvers                         false
% 8.03/1.48  --bc_imp_inh                            [conj_cone]
% 8.03/1.48  --conj_cone_tolerance                   3.
% 8.03/1.48  --extra_neg_conj                        none
% 8.03/1.48  --large_theory_mode                     true
% 8.03/1.48  --prolific_symb_bound                   200
% 8.03/1.48  --lt_threshold                          2000
% 8.03/1.48  --clause_weak_htbl                      true
% 8.03/1.48  --gc_record_bc_elim                     false
% 8.03/1.48  
% 8.03/1.48  ------ Preprocessing Options
% 8.03/1.48  
% 8.03/1.48  --preprocessing_flag                    true
% 8.03/1.48  --time_out_prep_mult                    0.1
% 8.03/1.48  --splitting_mode                        input
% 8.03/1.48  --splitting_grd                         true
% 8.03/1.48  --splitting_cvd                         false
% 8.03/1.48  --splitting_cvd_svl                     false
% 8.03/1.48  --splitting_nvd                         32
% 8.03/1.48  --sub_typing                            true
% 8.03/1.48  --prep_gs_sim                           true
% 8.03/1.48  --prep_unflatten                        true
% 8.03/1.48  --prep_res_sim                          true
% 8.03/1.48  --prep_upred                            true
% 8.03/1.48  --prep_sem_filter                       exhaustive
% 8.03/1.48  --prep_sem_filter_out                   false
% 8.03/1.48  --pred_elim                             true
% 8.03/1.48  --res_sim_input                         true
% 8.03/1.48  --eq_ax_congr_red                       true
% 8.03/1.48  --pure_diseq_elim                       true
% 8.03/1.48  --brand_transform                       false
% 8.03/1.48  --non_eq_to_eq                          false
% 8.03/1.48  --prep_def_merge                        true
% 8.03/1.48  --prep_def_merge_prop_impl              false
% 8.03/1.48  --prep_def_merge_mbd                    true
% 8.03/1.48  --prep_def_merge_tr_red                 false
% 8.03/1.48  --prep_def_merge_tr_cl                  false
% 8.03/1.48  --smt_preprocessing                     true
% 8.03/1.48  --smt_ac_axioms                         fast
% 8.03/1.48  --preprocessed_out                      false
% 8.03/1.48  --preprocessed_stats                    false
% 8.03/1.48  
% 8.03/1.48  ------ Abstraction refinement Options
% 8.03/1.48  
% 8.03/1.48  --abstr_ref                             []
% 8.03/1.48  --abstr_ref_prep                        false
% 8.03/1.48  --abstr_ref_until_sat                   false
% 8.03/1.48  --abstr_ref_sig_restrict                funpre
% 8.03/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 8.03/1.48  --abstr_ref_under                       []
% 8.03/1.48  
% 8.03/1.48  ------ SAT Options
% 8.03/1.48  
% 8.03/1.48  --sat_mode                              false
% 8.03/1.48  --sat_fm_restart_options                ""
% 8.03/1.48  --sat_gr_def                            false
% 8.03/1.48  --sat_epr_types                         true
% 8.03/1.48  --sat_non_cyclic_types                  false
% 8.03/1.48  --sat_finite_models                     false
% 8.03/1.48  --sat_fm_lemmas                         false
% 8.03/1.48  --sat_fm_prep                           false
% 8.03/1.48  --sat_fm_uc_incr                        true
% 8.03/1.48  --sat_out_model                         small
% 8.03/1.48  --sat_out_clauses                       false
% 8.03/1.48  
% 8.03/1.48  ------ QBF Options
% 8.03/1.48  
% 8.03/1.48  --qbf_mode                              false
% 8.03/1.48  --qbf_elim_univ                         false
% 8.03/1.48  --qbf_dom_inst                          none
% 8.03/1.48  --qbf_dom_pre_inst                      false
% 8.03/1.48  --qbf_sk_in                             false
% 8.03/1.48  --qbf_pred_elim                         true
% 8.03/1.48  --qbf_split                             512
% 8.03/1.48  
% 8.03/1.48  ------ BMC1 Options
% 8.03/1.48  
% 8.03/1.48  --bmc1_incremental                      false
% 8.03/1.48  --bmc1_axioms                           reachable_all
% 8.03/1.48  --bmc1_min_bound                        0
% 8.03/1.48  --bmc1_max_bound                        -1
% 8.03/1.48  --bmc1_max_bound_default                -1
% 8.03/1.48  --bmc1_symbol_reachability              true
% 8.03/1.48  --bmc1_property_lemmas                  false
% 8.03/1.48  --bmc1_k_induction                      false
% 8.03/1.48  --bmc1_non_equiv_states                 false
% 8.03/1.48  --bmc1_deadlock                         false
% 8.03/1.48  --bmc1_ucm                              false
% 8.03/1.48  --bmc1_add_unsat_core                   none
% 8.03/1.48  --bmc1_unsat_core_children              false
% 8.03/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 8.03/1.48  --bmc1_out_stat                         full
% 8.03/1.48  --bmc1_ground_init                      false
% 8.03/1.48  --bmc1_pre_inst_next_state              false
% 8.03/1.48  --bmc1_pre_inst_state                   false
% 8.03/1.48  --bmc1_pre_inst_reach_state             false
% 8.03/1.48  --bmc1_out_unsat_core                   false
% 8.03/1.48  --bmc1_aig_witness_out                  false
% 8.03/1.48  --bmc1_verbose                          false
% 8.03/1.48  --bmc1_dump_clauses_tptp                false
% 8.03/1.48  --bmc1_dump_unsat_core_tptp             false
% 8.03/1.48  --bmc1_dump_file                        -
% 8.03/1.48  --bmc1_ucm_expand_uc_limit              128
% 8.03/1.48  --bmc1_ucm_n_expand_iterations          6
% 8.03/1.48  --bmc1_ucm_extend_mode                  1
% 8.03/1.48  --bmc1_ucm_init_mode                    2
% 8.03/1.48  --bmc1_ucm_cone_mode                    none
% 8.03/1.48  --bmc1_ucm_reduced_relation_type        0
% 8.03/1.48  --bmc1_ucm_relax_model                  4
% 8.03/1.48  --bmc1_ucm_full_tr_after_sat            true
% 8.03/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 8.03/1.48  --bmc1_ucm_layered_model                none
% 8.03/1.48  --bmc1_ucm_max_lemma_size               10
% 8.03/1.48  
% 8.03/1.48  ------ AIG Options
% 8.03/1.48  
% 8.03/1.48  --aig_mode                              false
% 8.03/1.48  
% 8.03/1.48  ------ Instantiation Options
% 8.03/1.48  
% 8.03/1.48  --instantiation_flag                    true
% 8.03/1.48  --inst_sos_flag                         true
% 8.03/1.48  --inst_sos_phase                        true
% 8.03/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.03/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.03/1.48  --inst_lit_sel_side                     none
% 8.03/1.48  --inst_solver_per_active                1400
% 8.03/1.48  --inst_solver_calls_frac                1.
% 8.03/1.48  --inst_passive_queue_type               priority_queues
% 8.03/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.03/1.48  --inst_passive_queues_freq              [25;2]
% 8.03/1.48  --inst_dismatching                      true
% 8.03/1.48  --inst_eager_unprocessed_to_passive     true
% 8.03/1.48  --inst_prop_sim_given                   true
% 8.03/1.48  --inst_prop_sim_new                     false
% 8.03/1.48  --inst_subs_new                         false
% 8.03/1.48  --inst_eq_res_simp                      false
% 8.03/1.48  --inst_subs_given                       false
% 8.03/1.48  --inst_orphan_elimination               true
% 8.03/1.48  --inst_learning_loop_flag               true
% 8.03/1.48  --inst_learning_start                   3000
% 8.03/1.48  --inst_learning_factor                  2
% 8.03/1.48  --inst_start_prop_sim_after_learn       3
% 8.03/1.48  --inst_sel_renew                        solver
% 8.03/1.48  --inst_lit_activity_flag                true
% 8.03/1.48  --inst_restr_to_given                   false
% 8.03/1.48  --inst_activity_threshold               500
% 8.03/1.48  --inst_out_proof                        true
% 8.03/1.48  
% 8.03/1.48  ------ Resolution Options
% 8.03/1.48  
% 8.03/1.48  --resolution_flag                       false
% 8.03/1.48  --res_lit_sel                           adaptive
% 8.03/1.48  --res_lit_sel_side                      none
% 8.03/1.48  --res_ordering                          kbo
% 8.03/1.48  --res_to_prop_solver                    active
% 8.03/1.48  --res_prop_simpl_new                    false
% 8.03/1.48  --res_prop_simpl_given                  true
% 8.03/1.48  --res_passive_queue_type                priority_queues
% 8.03/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.03/1.48  --res_passive_queues_freq               [15;5]
% 8.03/1.48  --res_forward_subs                      full
% 8.03/1.48  --res_backward_subs                     full
% 8.03/1.48  --res_forward_subs_resolution           true
% 8.03/1.48  --res_backward_subs_resolution          true
% 8.03/1.48  --res_orphan_elimination                true
% 8.03/1.48  --res_time_limit                        2.
% 8.03/1.48  --res_out_proof                         true
% 8.03/1.48  
% 8.03/1.48  ------ Superposition Options
% 8.03/1.48  
% 8.03/1.48  --superposition_flag                    true
% 8.03/1.48  --sup_passive_queue_type                priority_queues
% 8.03/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.03/1.48  --sup_passive_queues_freq               [8;1;4]
% 8.03/1.48  --demod_completeness_check              fast
% 8.03/1.48  --demod_use_ground                      true
% 8.03/1.48  --sup_to_prop_solver                    passive
% 8.03/1.48  --sup_prop_simpl_new                    true
% 8.03/1.48  --sup_prop_simpl_given                  true
% 8.03/1.48  --sup_fun_splitting                     true
% 8.03/1.48  --sup_smt_interval                      50000
% 8.03/1.48  
% 8.03/1.48  ------ Superposition Simplification Setup
% 8.03/1.48  
% 8.03/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.03/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.03/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.03/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.03/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 8.03/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.03/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.03/1.48  --sup_immed_triv                        [TrivRules]
% 8.03/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.48  --sup_immed_bw_main                     []
% 8.03/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.03/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 8.03/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.48  --sup_input_bw                          []
% 8.03/1.48  
% 8.03/1.48  ------ Combination Options
% 8.03/1.48  
% 8.03/1.48  --comb_res_mult                         3
% 8.03/1.48  --comb_sup_mult                         2
% 8.03/1.48  --comb_inst_mult                        10
% 8.03/1.48  
% 8.03/1.48  ------ Debug Options
% 8.03/1.48  
% 8.03/1.48  --dbg_backtrace                         false
% 8.03/1.48  --dbg_dump_prop_clauses                 false
% 8.03/1.48  --dbg_dump_prop_clauses_file            -
% 8.03/1.48  --dbg_out_stat                          false
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  ------ Proving...
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  % SZS status Theorem for theBenchmark.p
% 8.03/1.48  
% 8.03/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 8.03/1.48  
% 8.03/1.48  fof(f6,axiom,(
% 8.03/1.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f14,plain,(
% 8.03/1.48    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.03/1.48    inference(ennf_transformation,[],[f6])).
% 8.03/1.48  
% 8.03/1.48  fof(f15,plain,(
% 8.03/1.48    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.03/1.48    inference(flattening,[],[f14])).
% 8.03/1.48  
% 8.03/1.48  fof(f43,plain,(
% 8.03/1.48    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f15])).
% 8.03/1.48  
% 8.03/1.48  fof(f4,axiom,(
% 8.03/1.48    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f11,plain,(
% 8.03/1.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 8.03/1.48    inference(ennf_transformation,[],[f4])).
% 8.03/1.48  
% 8.03/1.48  fof(f12,plain,(
% 8.03/1.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 8.03/1.48    inference(flattening,[],[f11])).
% 8.03/1.48  
% 8.03/1.48  fof(f39,plain,(
% 8.03/1.48    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f12])).
% 8.03/1.48  
% 8.03/1.48  fof(f7,axiom,(
% 8.03/1.48    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f45,plain,(
% 8.03/1.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 8.03/1.48    inference(cnf_transformation,[],[f7])).
% 8.03/1.48  
% 8.03/1.48  fof(f5,axiom,(
% 8.03/1.48    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f13,plain,(
% 8.03/1.48    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))) | ~v1_relat_1(X3))),
% 8.03/1.48    inference(ennf_transformation,[],[f5])).
% 8.03/1.48  
% 8.03/1.48  fof(f25,plain,(
% 8.03/1.48    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | (~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)))) | ~v1_relat_1(X3))),
% 8.03/1.48    inference(nnf_transformation,[],[f13])).
% 8.03/1.48  
% 8.03/1.48  fof(f26,plain,(
% 8.03/1.48    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)))) | ~v1_relat_1(X3))),
% 8.03/1.48    inference(flattening,[],[f25])).
% 8.03/1.48  
% 8.03/1.48  fof(f42,plain,(
% 8.03/1.48    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2) | ~v1_relat_1(X3)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f26])).
% 8.03/1.48  
% 8.03/1.48  fof(f8,axiom,(
% 8.03/1.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f16,plain,(
% 8.03/1.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 8.03/1.48    inference(ennf_transformation,[],[f8])).
% 8.03/1.48  
% 8.03/1.48  fof(f17,plain,(
% 8.03/1.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 8.03/1.48    inference(flattening,[],[f16])).
% 8.03/1.48  
% 8.03/1.48  fof(f27,plain,(
% 8.03/1.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 8.03/1.48    inference(nnf_transformation,[],[f17])).
% 8.03/1.48  
% 8.03/1.48  fof(f28,plain,(
% 8.03/1.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 8.03/1.48    inference(flattening,[],[f27])).
% 8.03/1.48  
% 8.03/1.48  fof(f49,plain,(
% 8.03/1.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f28])).
% 8.03/1.48  
% 8.03/1.48  fof(f65,plain,(
% 8.03/1.48    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 8.03/1.48    inference(equality_resolution,[],[f49])).
% 8.03/1.48  
% 8.03/1.48  fof(f46,plain,(
% 8.03/1.48    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 8.03/1.48    inference(cnf_transformation,[],[f7])).
% 8.03/1.48  
% 8.03/1.48  fof(f1,axiom,(
% 8.03/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f31,plain,(
% 8.03/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f1])).
% 8.03/1.48  
% 8.03/1.48  fof(f3,axiom,(
% 8.03/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f38,plain,(
% 8.03/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 8.03/1.48    inference(cnf_transformation,[],[f3])).
% 8.03/1.48  
% 8.03/1.48  fof(f54,plain,(
% 8.03/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 8.03/1.48    inference(definition_unfolding,[],[f31,f38,f38])).
% 8.03/1.48  
% 8.03/1.48  fof(f9,conjecture,(
% 8.03/1.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f10,negated_conjecture,(
% 8.03/1.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 8.03/1.48    inference(negated_conjecture,[],[f9])).
% 8.03/1.48  
% 8.03/1.48  fof(f18,plain,(
% 8.03/1.48    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 8.03/1.48    inference(ennf_transformation,[],[f10])).
% 8.03/1.48  
% 8.03/1.48  fof(f19,plain,(
% 8.03/1.48    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 8.03/1.48    inference(flattening,[],[f18])).
% 8.03/1.48  
% 8.03/1.48  fof(f29,plain,(
% 8.03/1.48    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) & r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 8.03/1.48    introduced(choice_axiom,[])).
% 8.03/1.48  
% 8.03/1.48  fof(f30,plain,(
% 8.03/1.48    k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) & r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 8.03/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f29])).
% 8.03/1.48  
% 8.03/1.48  fof(f52,plain,(
% 8.03/1.48    r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))),
% 8.03/1.48    inference(cnf_transformation,[],[f30])).
% 8.03/1.48  
% 8.03/1.48  fof(f61,plain,(
% 8.03/1.48    r2_hidden(sK1,k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),sK2)))),
% 8.03/1.48    inference(definition_unfolding,[],[f52,f38])).
% 8.03/1.48  
% 8.03/1.48  fof(f2,axiom,(
% 8.03/1.48    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 8.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f20,plain,(
% 8.03/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 8.03/1.48    inference(nnf_transformation,[],[f2])).
% 8.03/1.48  
% 8.03/1.48  fof(f21,plain,(
% 8.03/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 8.03/1.48    inference(flattening,[],[f20])).
% 8.03/1.48  
% 8.03/1.48  fof(f22,plain,(
% 8.03/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 8.03/1.48    inference(rectify,[],[f21])).
% 8.03/1.48  
% 8.03/1.48  fof(f23,plain,(
% 8.03/1.48    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 8.03/1.48    introduced(choice_axiom,[])).
% 8.03/1.48  
% 8.03/1.48  fof(f24,plain,(
% 8.03/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 8.03/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 8.03/1.48  
% 8.03/1.48  fof(f33,plain,(
% 8.03/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 8.03/1.48    inference(cnf_transformation,[],[f24])).
% 8.03/1.48  
% 8.03/1.48  fof(f59,plain,(
% 8.03/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 8.03/1.48    inference(definition_unfolding,[],[f33,f38])).
% 8.03/1.48  
% 8.03/1.48  fof(f63,plain,(
% 8.03/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 8.03/1.48    inference(equality_resolution,[],[f59])).
% 8.03/1.48  
% 8.03/1.48  fof(f32,plain,(
% 8.03/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 8.03/1.48    inference(cnf_transformation,[],[f24])).
% 8.03/1.48  
% 8.03/1.48  fof(f60,plain,(
% 8.03/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 8.03/1.48    inference(definition_unfolding,[],[f32,f38])).
% 8.03/1.48  
% 8.03/1.48  fof(f64,plain,(
% 8.03/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 8.03/1.48    inference(equality_resolution,[],[f60])).
% 8.03/1.48  
% 8.03/1.48  fof(f44,plain,(
% 8.03/1.48    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f15])).
% 8.03/1.48  
% 8.03/1.48  fof(f48,plain,(
% 8.03/1.48    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f28])).
% 8.03/1.48  
% 8.03/1.48  fof(f53,plain,(
% 8.03/1.48    k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)),
% 8.03/1.48    inference(cnf_transformation,[],[f30])).
% 8.03/1.48  
% 8.03/1.48  fof(f51,plain,(
% 8.03/1.48    v1_funct_1(sK3)),
% 8.03/1.48    inference(cnf_transformation,[],[f30])).
% 8.03/1.48  
% 8.03/1.48  fof(f50,plain,(
% 8.03/1.48    v1_relat_1(sK3)),
% 8.03/1.48    inference(cnf_transformation,[],[f30])).
% 8.03/1.48  
% 8.03/1.48  cnf(c_12,plain,
% 8.03/1.48      ( ~ v1_funct_1(X0)
% 8.03/1.48      | ~ v1_funct_1(X1)
% 8.03/1.48      | ~ v1_relat_1(X0)
% 8.03/1.48      | ~ v1_relat_1(X1)
% 8.03/1.48      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 8.03/1.48      inference(cnf_transformation,[],[f43]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_7,plain,
% 8.03/1.48      ( ~ v1_relat_1(X0)
% 8.03/1.48      | ~ v1_relat_1(X1)
% 8.03/1.48      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 8.03/1.48      inference(cnf_transformation,[],[f39]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_122,plain,
% 8.03/1.48      ( ~ v1_relat_1(X0)
% 8.03/1.48      | ~ v1_relat_1(X1)
% 8.03/1.48      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 8.03/1.48      inference(global_propositional_subsumption,
% 8.03/1.48                [status(thm)],
% 8.03/1.48                [c_12,c_7]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_123,plain,
% 8.03/1.48      ( ~ v1_relat_1(X0)
% 8.03/1.48      | ~ v1_relat_1(X1)
% 8.03/1.48      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 8.03/1.48      inference(renaming,[status(thm)],[c_122]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_1121,plain,
% 8.03/1.48      ( v1_relat_1(k5_relat_1(k6_relat_1(X0),sK3))
% 8.03/1.48      | ~ v1_relat_1(k6_relat_1(X0))
% 8.03/1.48      | ~ v1_relat_1(sK3) ),
% 8.03/1.48      inference(instantiation,[status(thm)],[c_123]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_14911,plain,
% 8.03/1.48      ( v1_relat_1(k5_relat_1(k6_relat_1(sK2),sK3))
% 8.03/1.48      | ~ v1_relat_1(k6_relat_1(sK2))
% 8.03/1.48      | ~ v1_relat_1(sK3) ),
% 8.03/1.48      inference(instantiation,[status(thm)],[c_1121]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_14,plain,
% 8.03/1.48      ( v1_relat_1(k6_relat_1(X0)) ),
% 8.03/1.48      inference(cnf_transformation,[],[f45]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_5910,plain,
% 8.03/1.48      ( v1_relat_1(k6_relat_1(sK2)) ),
% 8.03/1.48      inference(instantiation,[status(thm)],[c_14]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_8,plain,
% 8.03/1.48      ( ~ r2_hidden(X0,X1)
% 8.03/1.48      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 8.03/1.48      | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3))
% 8.03/1.48      | ~ v1_relat_1(X3) ),
% 8.03/1.48      inference(cnf_transformation,[],[f42]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_990,plain,
% 8.03/1.48      ( r2_hidden(k4_tarski(sK1,X0),k5_relat_1(k6_relat_1(X1),sK3))
% 8.03/1.48      | ~ r2_hidden(k4_tarski(sK1,X0),sK3)
% 8.03/1.48      | ~ r2_hidden(sK1,X1)
% 8.03/1.48      | ~ v1_relat_1(sK3) ),
% 8.03/1.48      inference(instantiation,[status(thm)],[c_8]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_4072,plain,
% 8.03/1.48      ( r2_hidden(k4_tarski(sK1,X0),k5_relat_1(k6_relat_1(sK2),sK3))
% 8.03/1.48      | ~ r2_hidden(k4_tarski(sK1,X0),sK3)
% 8.03/1.48      | ~ r2_hidden(sK1,sK2)
% 8.03/1.48      | ~ v1_relat_1(sK3) ),
% 8.03/1.48      inference(instantiation,[status(thm)],[c_990]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_4746,plain,
% 8.03/1.48      ( r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),k5_relat_1(k6_relat_1(sK2),sK3))
% 8.03/1.48      | ~ r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),sK3)
% 8.03/1.48      | ~ r2_hidden(sK1,sK2)
% 8.03/1.48      | ~ v1_relat_1(sK3) ),
% 8.03/1.48      inference(instantiation,[status(thm)],[c_4072]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_15,plain,
% 8.03/1.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 8.03/1.48      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 8.03/1.48      | ~ v1_funct_1(X1)
% 8.03/1.48      | ~ v1_relat_1(X1) ),
% 8.03/1.48      inference(cnf_transformation,[],[f65]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_3063,plain,
% 8.03/1.48      ( r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),sK3)
% 8.03/1.48      | ~ r2_hidden(sK1,k1_relat_1(sK3))
% 8.03/1.48      | ~ v1_funct_1(sK3)
% 8.03/1.48      | ~ v1_relat_1(sK3) ),
% 8.03/1.48      inference(instantiation,[status(thm)],[c_15]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_13,plain,
% 8.03/1.48      ( v1_funct_1(k6_relat_1(X0)) ),
% 8.03/1.48      inference(cnf_transformation,[],[f46]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_2191,plain,
% 8.03/1.48      ( v1_funct_1(k6_relat_1(sK2)) ),
% 8.03/1.48      inference(instantiation,[status(thm)],[c_13]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_0,plain,
% 8.03/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.03/1.48      inference(cnf_transformation,[],[f54]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_19,negated_conjecture,
% 8.03/1.48      ( r2_hidden(sK1,k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),sK2))) ),
% 8.03/1.48      inference(cnf_transformation,[],[f61]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_560,plain,
% 8.03/1.48      ( r2_hidden(sK1,k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),sK2))) = iProver_top ),
% 8.03/1.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_1153,plain,
% 8.03/1.48      ( r2_hidden(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 8.03/1.48      inference(demodulation,[status(thm)],[c_0,c_560]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_5,plain,
% 8.03/1.48      ( r2_hidden(X0,X1)
% 8.03/1.48      | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 8.03/1.48      inference(cnf_transformation,[],[f63]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_572,plain,
% 8.03/1.48      ( r2_hidden(X0,X1) = iProver_top
% 8.03/1.48      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 8.03/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_1496,plain,
% 8.03/1.48      ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
% 8.03/1.48      inference(superposition,[status(thm)],[c_1153,c_572]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_1501,plain,
% 8.03/1.48      ( r2_hidden(sK1,k1_relat_1(sK3)) ),
% 8.03/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_1496]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_6,plain,
% 8.03/1.48      ( r2_hidden(X0,X1)
% 8.03/1.48      | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 8.03/1.48      inference(cnf_transformation,[],[f64]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_571,plain,
% 8.03/1.48      ( r2_hidden(X0,X1) = iProver_top
% 8.03/1.48      | r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top ),
% 8.03/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_1322,plain,
% 8.03/1.48      ( r2_hidden(sK1,sK2) = iProver_top ),
% 8.03/1.48      inference(superposition,[status(thm)],[c_1153,c_571]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_1327,plain,
% 8.03/1.48      ( r2_hidden(sK1,sK2) ),
% 8.03/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_1322]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_11,plain,
% 8.03/1.48      ( ~ v1_funct_1(X0)
% 8.03/1.48      | ~ v1_funct_1(X1)
% 8.03/1.48      | v1_funct_1(k5_relat_1(X1,X0))
% 8.03/1.48      | ~ v1_relat_1(X0)
% 8.03/1.48      | ~ v1_relat_1(X1) ),
% 8.03/1.48      inference(cnf_transformation,[],[f44]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_1296,plain,
% 8.03/1.48      ( v1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3))
% 8.03/1.48      | ~ v1_funct_1(k6_relat_1(sK2))
% 8.03/1.48      | ~ v1_funct_1(sK3)
% 8.03/1.48      | ~ v1_relat_1(k6_relat_1(sK2))
% 8.03/1.48      | ~ v1_relat_1(sK3) ),
% 8.03/1.48      inference(instantiation,[status(thm)],[c_11]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_16,plain,
% 8.03/1.48      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 8.03/1.48      | ~ v1_funct_1(X2)
% 8.03/1.48      | ~ v1_relat_1(X2)
% 8.03/1.48      | k1_funct_1(X2,X0) = X1 ),
% 8.03/1.48      inference(cnf_transformation,[],[f48]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_910,plain,
% 8.03/1.48      ( ~ r2_hidden(k4_tarski(sK1,k1_funct_1(sK3,sK1)),k5_relat_1(k6_relat_1(sK2),sK3))
% 8.03/1.48      | ~ v1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3))
% 8.03/1.48      | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK2),sK3))
% 8.03/1.48      | k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) = k1_funct_1(sK3,sK1) ),
% 8.03/1.48      inference(instantiation,[status(thm)],[c_16]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_232,plain,( X0 = X0 ),theory(equality) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_725,plain,
% 8.03/1.48      ( k1_funct_1(sK3,sK1) = k1_funct_1(sK3,sK1) ),
% 8.03/1.48      inference(instantiation,[status(thm)],[c_232]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_233,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_602,plain,
% 8.03/1.48      ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) != X0
% 8.03/1.48      | k1_funct_1(sK3,sK1) != X0
% 8.03/1.48      | k1_funct_1(sK3,sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
% 8.03/1.48      inference(instantiation,[status(thm)],[c_233]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_640,plain,
% 8.03/1.48      ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) != k1_funct_1(sK3,sK1)
% 8.03/1.48      | k1_funct_1(sK3,sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
% 8.03/1.48      | k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
% 8.03/1.48      inference(instantiation,[status(thm)],[c_602]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_18,negated_conjecture,
% 8.03/1.48      ( k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
% 8.03/1.48      inference(cnf_transformation,[],[f53]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_20,negated_conjecture,
% 8.03/1.48      ( v1_funct_1(sK3) ),
% 8.03/1.48      inference(cnf_transformation,[],[f51]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(c_21,negated_conjecture,
% 8.03/1.48      ( v1_relat_1(sK3) ),
% 8.03/1.48      inference(cnf_transformation,[],[f50]) ).
% 8.03/1.48  
% 8.03/1.48  cnf(contradiction,plain,
% 8.03/1.48      ( $false ),
% 8.03/1.48      inference(minisat,
% 8.03/1.48                [status(thm)],
% 8.03/1.48                [c_14911,c_5910,c_4746,c_3063,c_2191,c_1501,c_1327,
% 8.03/1.48                 c_1296,c_910,c_725,c_640,c_18,c_20,c_21]) ).
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 8.03/1.48  
% 8.03/1.48  ------                               Statistics
% 8.03/1.48  
% 8.03/1.48  ------ General
% 8.03/1.48  
% 8.03/1.48  abstr_ref_over_cycles:                  0
% 8.03/1.48  abstr_ref_under_cycles:                 0
% 8.03/1.48  gc_basic_clause_elim:                   0
% 8.03/1.48  forced_gc_time:                         0
% 8.03/1.48  parsing_time:                           0.007
% 8.03/1.48  unif_index_cands_time:                  0.
% 8.03/1.48  unif_index_add_time:                    0.
% 8.03/1.48  orderings_time:                         0.
% 8.03/1.48  out_proof_time:                         0.007
% 8.03/1.48  total_time:                             0.997
% 8.03/1.48  num_of_symbols:                         44
% 8.03/1.48  num_of_terms:                           35288
% 8.03/1.48  
% 8.03/1.48  ------ Preprocessing
% 8.03/1.48  
% 8.03/1.48  num_of_splits:                          0
% 8.03/1.48  num_of_split_atoms:                     0
% 8.03/1.48  num_of_reused_defs:                     0
% 8.03/1.48  num_eq_ax_congr_red:                    8
% 8.03/1.48  num_of_sem_filtered_clauses:            1
% 8.03/1.48  num_of_subtypes:                        0
% 8.03/1.48  monotx_restored_types:                  0
% 8.03/1.48  sat_num_of_epr_types:                   0
% 8.03/1.48  sat_num_of_non_cyclic_types:            0
% 8.03/1.48  sat_guarded_non_collapsed_types:        0
% 8.03/1.48  num_pure_diseq_elim:                    0
% 8.03/1.48  simp_replaced_by:                       0
% 8.03/1.48  res_preprocessed:                       89
% 8.03/1.48  prep_upred:                             0
% 8.03/1.48  prep_unflattend:                        0
% 8.03/1.48  smt_new_axioms:                         0
% 8.03/1.48  pred_elim_cands:                        3
% 8.03/1.48  pred_elim:                              0
% 8.03/1.48  pred_elim_cl:                           0
% 8.03/1.48  pred_elim_cycles:                       1
% 8.03/1.48  merged_defs:                            0
% 8.03/1.48  merged_defs_ncl:                        0
% 8.03/1.48  bin_hyper_res:                          0
% 8.03/1.48  prep_cycles:                            3
% 8.03/1.48  pred_elim_time:                         0.
% 8.03/1.48  splitting_time:                         0.
% 8.03/1.48  sem_filter_time:                        0.
% 8.03/1.48  monotx_time:                            0.
% 8.03/1.48  subtype_inf_time:                       0.
% 8.03/1.48  
% 8.03/1.48  ------ Problem properties
% 8.03/1.48  
% 8.03/1.48  clauses:                                22
% 8.03/1.48  conjectures:                            4
% 8.03/1.48  epr:                                    2
% 8.03/1.48  horn:                                   20
% 8.03/1.48  ground:                                 4
% 8.03/1.48  unary:                                  7
% 8.03/1.48  binary:                                 2
% 8.03/1.48  lits:                                   57
% 8.03/1.48  lits_eq:                                6
% 8.03/1.48  fd_pure:                                0
% 8.03/1.48  fd_pseudo:                              0
% 8.03/1.48  fd_cond:                                0
% 8.03/1.48  fd_pseudo_cond:                         4
% 8.03/1.48  ac_symbols:                             0
% 8.03/1.48  
% 8.03/1.48  ------ Propositional Solver
% 8.03/1.48  
% 8.03/1.48  prop_solver_calls:                      26
% 8.03/1.48  prop_fast_solver_calls:                 767
% 8.03/1.48  smt_solver_calls:                       0
% 8.03/1.48  smt_fast_solver_calls:                  0
% 8.03/1.48  prop_num_of_clauses:                    10977
% 8.03/1.48  prop_preprocess_simplified:             13441
% 8.03/1.48  prop_fo_subsumed:                       2
% 8.03/1.48  prop_solver_time:                       0.
% 8.03/1.48  smt_solver_time:                        0.
% 8.03/1.48  smt_fast_solver_time:                   0.
% 8.03/1.48  prop_fast_solver_time:                  0.
% 8.03/1.48  prop_unsat_core_time:                   0.
% 8.03/1.48  
% 8.03/1.48  ------ QBF
% 8.03/1.48  
% 8.03/1.48  qbf_q_res:                              0
% 8.03/1.48  qbf_num_tautologies:                    0
% 8.03/1.48  qbf_prep_cycles:                        0
% 8.03/1.48  
% 8.03/1.48  ------ BMC1
% 8.03/1.48  
% 8.03/1.48  bmc1_current_bound:                     -1
% 8.03/1.48  bmc1_last_solved_bound:                 -1
% 8.03/1.48  bmc1_unsat_core_size:                   -1
% 8.03/1.48  bmc1_unsat_core_parents_size:           -1
% 8.03/1.48  bmc1_merge_next_fun:                    0
% 8.03/1.48  bmc1_unsat_core_clauses_time:           0.
% 8.03/1.48  
% 8.03/1.48  ------ Instantiation
% 8.03/1.48  
% 8.03/1.48  inst_num_of_clauses:                    1119
% 8.03/1.48  inst_num_in_passive:                    578
% 8.03/1.48  inst_num_in_active:                     533
% 8.03/1.48  inst_num_in_unprocessed:                8
% 8.03/1.48  inst_num_of_loops:                      571
% 8.03/1.48  inst_num_of_learning_restarts:          0
% 8.03/1.48  inst_num_moves_active_passive:          35
% 8.03/1.48  inst_lit_activity:                      0
% 8.03/1.48  inst_lit_activity_moves:                0
% 8.03/1.48  inst_num_tautologies:                   0
% 8.03/1.48  inst_num_prop_implied:                  0
% 8.03/1.48  inst_num_existing_simplified:           0
% 8.03/1.48  inst_num_eq_res_simplified:             0
% 8.03/1.48  inst_num_child_elim:                    0
% 8.03/1.48  inst_num_of_dismatching_blockings:      288
% 8.03/1.48  inst_num_of_non_proper_insts:           767
% 8.03/1.48  inst_num_of_duplicates:                 0
% 8.03/1.48  inst_inst_num_from_inst_to_res:         0
% 8.03/1.48  inst_dismatching_checking_time:         0.
% 8.03/1.48  
% 8.03/1.48  ------ Resolution
% 8.03/1.48  
% 8.03/1.48  res_num_of_clauses:                     0
% 8.03/1.48  res_num_in_passive:                     0
% 8.03/1.48  res_num_in_active:                      0
% 8.03/1.48  res_num_of_loops:                       92
% 8.03/1.48  res_forward_subset_subsumed:            65
% 8.03/1.48  res_backward_subset_subsumed:           2
% 8.03/1.48  res_forward_subsumed:                   0
% 8.03/1.48  res_backward_subsumed:                  0
% 8.03/1.48  res_forward_subsumption_resolution:     0
% 8.03/1.48  res_backward_subsumption_resolution:    0
% 8.03/1.48  res_clause_to_clause_subsumption:       90960
% 8.03/1.48  res_orphan_elimination:                 0
% 8.03/1.48  res_tautology_del:                      51
% 8.03/1.48  res_num_eq_res_simplified:              0
% 8.03/1.48  res_num_sel_changes:                    0
% 8.03/1.48  res_moves_from_active_to_pass:          0
% 8.03/1.48  
% 8.03/1.48  ------ Superposition
% 8.03/1.48  
% 8.03/1.48  sup_time_total:                         0.
% 8.03/1.48  sup_time_generating:                    0.
% 8.03/1.48  sup_time_sim_full:                      0.
% 8.03/1.48  sup_time_sim_immed:                     0.
% 8.03/1.48  
% 8.03/1.48  sup_num_of_clauses:                     2739
% 8.03/1.48  sup_num_in_active:                      113
% 8.03/1.48  sup_num_in_passive:                     2626
% 8.03/1.48  sup_num_of_loops:                       114
% 8.03/1.48  sup_fw_superposition:                   1344
% 8.03/1.48  sup_bw_superposition:                   1969
% 8.03/1.48  sup_immediate_simplified:               80
% 8.03/1.48  sup_given_eliminated:                   0
% 8.03/1.48  comparisons_done:                       0
% 8.03/1.48  comparisons_avoided:                    0
% 8.03/1.48  
% 8.03/1.48  ------ Simplifications
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  sim_fw_subset_subsumed:                 6
% 8.03/1.48  sim_bw_subset_subsumed:                 0
% 8.03/1.48  sim_fw_subsumed:                        72
% 8.03/1.48  sim_bw_subsumed:                        3
% 8.03/1.48  sim_fw_subsumption_res:                 0
% 8.03/1.48  sim_bw_subsumption_res:                 0
% 8.03/1.48  sim_tautology_del:                      62
% 8.03/1.48  sim_eq_tautology_del:                   1
% 8.03/1.48  sim_eq_res_simp:                        17
% 8.03/1.48  sim_fw_demodulated:                     0
% 8.03/1.48  sim_bw_demodulated:                     1
% 8.03/1.48  sim_light_normalised:                   0
% 8.03/1.48  sim_joinable_taut:                      0
% 8.03/1.48  sim_joinable_simp:                      0
% 8.03/1.48  sim_ac_normalised:                      0
% 8.03/1.48  sim_smt_subsumption:                    0
% 8.03/1.48  
%------------------------------------------------------------------------------

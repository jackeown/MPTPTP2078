%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:09 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 243 expanded)
%              Number of clauses        :   50 (  72 expanded)
%              Number of leaves         :   12 (  48 expanded)
%              Depth                    :   18
%              Number of atoms          :  305 (1101 expanded)
%              Number of equality atoms :   87 (  99 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK1,sK2)
      & v2_funct_1(sK3)
      & r1_tarski(sK1,k1_relat_1(sK3))
      & r1_tarski(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r1_tarski(sK1,sK2)
    & v2_funct_1(sK3)
    & r1_tarski(sK1,k1_relat_1(sK3))
    & r1_tarski(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f35])).

fof(f56,plain,(
    r1_tarski(sK1,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    r1_tarski(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f3,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f13])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK1,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1048,plain,
    ( r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1050,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_17,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_281,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_282,plain,
    ( r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,X0)),X0)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_286,plain,
    ( r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,X0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_282,c_21,c_20])).

cnf(c_1044,plain,
    ( r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1060,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1799,plain,
    ( k10_relat_1(sK3,k9_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,k10_relat_1(sK3,k9_relat_1(sK3,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_1060])).

cnf(c_1962,plain,
    ( k10_relat_1(sK3,k9_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1050,c_1799])).

cnf(c_22,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6099,plain,
    ( r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | k10_relat_1(sK3,k9_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1962,c_22])).

cnf(c_6100,plain,
    ( k10_relat_1(sK3,k9_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6099])).

cnf(c_6109,plain,
    ( k10_relat_1(sK3,k9_relat_1(sK3,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1048,c_6100])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1047,plain,
    ( r1_tarski(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_270,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_17])).

cnf(c_271,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k9_relat_1(k2_funct_1(sK3),X0) = k10_relat_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_275,plain,
    ( k9_relat_1(k2_funct_1(sK3),X0) = k10_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_271,c_21,c_20])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1053,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2033,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(k2_funct_1(sK3),X0),k10_relat_1(sK3,X1)) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_275,c_1053])).

cnf(c_2053,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k10_relat_1(sK3,X0),k10_relat_1(sK3,X1)) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2033,c_275])).

cnf(c_23,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_37,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_2389,plain,
    ( r1_tarski(k10_relat_1(sK3,X0),k10_relat_1(sK3,X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2053,c_22,c_23,c_39])).

cnf(c_2390,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k10_relat_1(sK3,X0),k10_relat_1(sK3,X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2389])).

cnf(c_5,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1056,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_tarski(X1),X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1054,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k3_tarski(X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2075,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1054])).

cnf(c_2257,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_2075])).

cnf(c_3226,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k10_relat_1(sK3,X1),X2) != iProver_top
    | r1_tarski(k10_relat_1(sK3,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2390,c_2257])).

cnf(c_4055,plain,
    ( r1_tarski(X0,k9_relat_1(sK3,X1)) != iProver_top
    | r1_tarski(k10_relat_1(sK3,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_3226])).

cnf(c_4225,plain,
    ( r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK1)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_4055])).

cnf(c_6246,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6109,c_4225])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,plain,
    ( r1_tarski(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6246,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.08/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.04  
% 3.08/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.08/1.04  
% 3.08/1.04  ------  iProver source info
% 3.08/1.04  
% 3.08/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.08/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.08/1.04  git: non_committed_changes: false
% 3.08/1.04  git: last_make_outside_of_git: false
% 3.08/1.04  
% 3.08/1.04  ------ 
% 3.08/1.04  
% 3.08/1.04  ------ Input Options
% 3.08/1.04  
% 3.08/1.04  --out_options                           all
% 3.08/1.04  --tptp_safe_out                         true
% 3.08/1.04  --problem_path                          ""
% 3.08/1.04  --include_path                          ""
% 3.08/1.04  --clausifier                            res/vclausify_rel
% 3.08/1.04  --clausifier_options                    --mode clausify
% 3.08/1.04  --stdin                                 false
% 3.08/1.04  --stats_out                             all
% 3.08/1.04  
% 3.08/1.04  ------ General Options
% 3.08/1.04  
% 3.08/1.04  --fof                                   false
% 3.08/1.04  --time_out_real                         305.
% 3.08/1.04  --time_out_virtual                      -1.
% 3.08/1.04  --symbol_type_check                     false
% 3.08/1.04  --clausify_out                          false
% 3.08/1.04  --sig_cnt_out                           false
% 3.08/1.04  --trig_cnt_out                          false
% 3.08/1.04  --trig_cnt_out_tolerance                1.
% 3.08/1.04  --trig_cnt_out_sk_spl                   false
% 3.08/1.04  --abstr_cl_out                          false
% 3.08/1.04  
% 3.08/1.04  ------ Global Options
% 3.08/1.04  
% 3.08/1.04  --schedule                              default
% 3.08/1.04  --add_important_lit                     false
% 3.08/1.04  --prop_solver_per_cl                    1000
% 3.08/1.04  --min_unsat_core                        false
% 3.08/1.04  --soft_assumptions                      false
% 3.08/1.04  --soft_lemma_size                       3
% 3.08/1.04  --prop_impl_unit_size                   0
% 3.08/1.04  --prop_impl_unit                        []
% 3.08/1.04  --share_sel_clauses                     true
% 3.08/1.04  --reset_solvers                         false
% 3.08/1.04  --bc_imp_inh                            [conj_cone]
% 3.08/1.04  --conj_cone_tolerance                   3.
% 3.08/1.04  --extra_neg_conj                        none
% 3.08/1.04  --large_theory_mode                     true
% 3.08/1.04  --prolific_symb_bound                   200
% 3.08/1.04  --lt_threshold                          2000
% 3.08/1.04  --clause_weak_htbl                      true
% 3.08/1.04  --gc_record_bc_elim                     false
% 3.08/1.04  
% 3.08/1.04  ------ Preprocessing Options
% 3.08/1.04  
% 3.08/1.04  --preprocessing_flag                    true
% 3.08/1.04  --time_out_prep_mult                    0.1
% 3.08/1.04  --splitting_mode                        input
% 3.08/1.04  --splitting_grd                         true
% 3.08/1.04  --splitting_cvd                         false
% 3.08/1.04  --splitting_cvd_svl                     false
% 3.08/1.04  --splitting_nvd                         32
% 3.08/1.04  --sub_typing                            true
% 3.08/1.04  --prep_gs_sim                           true
% 3.08/1.04  --prep_unflatten                        true
% 3.08/1.04  --prep_res_sim                          true
% 3.08/1.04  --prep_upred                            true
% 3.08/1.04  --prep_sem_filter                       exhaustive
% 3.08/1.04  --prep_sem_filter_out                   false
% 3.08/1.04  --pred_elim                             true
% 3.08/1.04  --res_sim_input                         true
% 3.08/1.04  --eq_ax_congr_red                       true
% 3.08/1.04  --pure_diseq_elim                       true
% 3.08/1.04  --brand_transform                       false
% 3.08/1.04  --non_eq_to_eq                          false
% 3.08/1.04  --prep_def_merge                        true
% 3.08/1.04  --prep_def_merge_prop_impl              false
% 3.08/1.04  --prep_def_merge_mbd                    true
% 3.08/1.04  --prep_def_merge_tr_red                 false
% 3.08/1.04  --prep_def_merge_tr_cl                  false
% 3.08/1.04  --smt_preprocessing                     true
% 3.08/1.04  --smt_ac_axioms                         fast
% 3.08/1.04  --preprocessed_out                      false
% 3.08/1.04  --preprocessed_stats                    false
% 3.08/1.04  
% 3.08/1.04  ------ Abstraction refinement Options
% 3.08/1.04  
% 3.08/1.04  --abstr_ref                             []
% 3.08/1.04  --abstr_ref_prep                        false
% 3.08/1.04  --abstr_ref_until_sat                   false
% 3.08/1.04  --abstr_ref_sig_restrict                funpre
% 3.08/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.08/1.04  --abstr_ref_under                       []
% 3.08/1.04  
% 3.08/1.04  ------ SAT Options
% 3.08/1.04  
% 3.08/1.04  --sat_mode                              false
% 3.08/1.04  --sat_fm_restart_options                ""
% 3.08/1.04  --sat_gr_def                            false
% 3.08/1.04  --sat_epr_types                         true
% 3.08/1.04  --sat_non_cyclic_types                  false
% 3.08/1.04  --sat_finite_models                     false
% 3.08/1.04  --sat_fm_lemmas                         false
% 3.08/1.04  --sat_fm_prep                           false
% 3.08/1.04  --sat_fm_uc_incr                        true
% 3.08/1.04  --sat_out_model                         small
% 3.08/1.04  --sat_out_clauses                       false
% 3.08/1.04  
% 3.08/1.04  ------ QBF Options
% 3.08/1.04  
% 3.08/1.04  --qbf_mode                              false
% 3.08/1.04  --qbf_elim_univ                         false
% 3.08/1.04  --qbf_dom_inst                          none
% 3.08/1.04  --qbf_dom_pre_inst                      false
% 3.08/1.04  --qbf_sk_in                             false
% 3.08/1.04  --qbf_pred_elim                         true
% 3.08/1.04  --qbf_split                             512
% 3.08/1.04  
% 3.08/1.04  ------ BMC1 Options
% 3.08/1.04  
% 3.08/1.04  --bmc1_incremental                      false
% 3.08/1.04  --bmc1_axioms                           reachable_all
% 3.08/1.04  --bmc1_min_bound                        0
% 3.08/1.04  --bmc1_max_bound                        -1
% 3.08/1.04  --bmc1_max_bound_default                -1
% 3.08/1.04  --bmc1_symbol_reachability              true
% 3.08/1.04  --bmc1_property_lemmas                  false
% 3.08/1.04  --bmc1_k_induction                      false
% 3.08/1.04  --bmc1_non_equiv_states                 false
% 3.08/1.04  --bmc1_deadlock                         false
% 3.08/1.04  --bmc1_ucm                              false
% 3.08/1.04  --bmc1_add_unsat_core                   none
% 3.08/1.04  --bmc1_unsat_core_children              false
% 3.08/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.08/1.04  --bmc1_out_stat                         full
% 3.08/1.04  --bmc1_ground_init                      false
% 3.08/1.04  --bmc1_pre_inst_next_state              false
% 3.08/1.04  --bmc1_pre_inst_state                   false
% 3.08/1.04  --bmc1_pre_inst_reach_state             false
% 3.08/1.04  --bmc1_out_unsat_core                   false
% 3.08/1.04  --bmc1_aig_witness_out                  false
% 3.08/1.04  --bmc1_verbose                          false
% 3.08/1.04  --bmc1_dump_clauses_tptp                false
% 3.08/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.08/1.04  --bmc1_dump_file                        -
% 3.08/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.08/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.08/1.04  --bmc1_ucm_extend_mode                  1
% 3.08/1.04  --bmc1_ucm_init_mode                    2
% 3.08/1.04  --bmc1_ucm_cone_mode                    none
% 3.08/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.08/1.04  --bmc1_ucm_relax_model                  4
% 3.08/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.08/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.08/1.04  --bmc1_ucm_layered_model                none
% 3.08/1.04  --bmc1_ucm_max_lemma_size               10
% 3.08/1.04  
% 3.08/1.04  ------ AIG Options
% 3.08/1.04  
% 3.08/1.04  --aig_mode                              false
% 3.08/1.04  
% 3.08/1.04  ------ Instantiation Options
% 3.08/1.04  
% 3.08/1.04  --instantiation_flag                    true
% 3.08/1.04  --inst_sos_flag                         false
% 3.08/1.04  --inst_sos_phase                        true
% 3.08/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.08/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.08/1.04  --inst_lit_sel_side                     num_symb
% 3.08/1.04  --inst_solver_per_active                1400
% 3.08/1.04  --inst_solver_calls_frac                1.
% 3.08/1.04  --inst_passive_queue_type               priority_queues
% 3.08/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.08/1.04  --inst_passive_queues_freq              [25;2]
% 3.08/1.04  --inst_dismatching                      true
% 3.08/1.04  --inst_eager_unprocessed_to_passive     true
% 3.08/1.04  --inst_prop_sim_given                   true
% 3.08/1.04  --inst_prop_sim_new                     false
% 3.08/1.04  --inst_subs_new                         false
% 3.08/1.04  --inst_eq_res_simp                      false
% 3.08/1.04  --inst_subs_given                       false
% 3.08/1.04  --inst_orphan_elimination               true
% 3.08/1.04  --inst_learning_loop_flag               true
% 3.08/1.04  --inst_learning_start                   3000
% 3.08/1.04  --inst_learning_factor                  2
% 3.08/1.04  --inst_start_prop_sim_after_learn       3
% 3.08/1.04  --inst_sel_renew                        solver
% 3.08/1.04  --inst_lit_activity_flag                true
% 3.08/1.04  --inst_restr_to_given                   false
% 3.08/1.04  --inst_activity_threshold               500
% 3.08/1.04  --inst_out_proof                        true
% 3.08/1.04  
% 3.08/1.04  ------ Resolution Options
% 3.08/1.04  
% 3.08/1.04  --resolution_flag                       true
% 3.08/1.04  --res_lit_sel                           adaptive
% 3.08/1.04  --res_lit_sel_side                      none
% 3.08/1.04  --res_ordering                          kbo
% 3.08/1.04  --res_to_prop_solver                    active
% 3.08/1.04  --res_prop_simpl_new                    false
% 3.08/1.04  --res_prop_simpl_given                  true
% 3.08/1.04  --res_passive_queue_type                priority_queues
% 3.08/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.08/1.04  --res_passive_queues_freq               [15;5]
% 3.08/1.04  --res_forward_subs                      full
% 3.08/1.04  --res_backward_subs                     full
% 3.08/1.04  --res_forward_subs_resolution           true
% 3.08/1.04  --res_backward_subs_resolution          true
% 3.08/1.04  --res_orphan_elimination                true
% 3.08/1.04  --res_time_limit                        2.
% 3.08/1.04  --res_out_proof                         true
% 3.08/1.04  
% 3.08/1.04  ------ Superposition Options
% 3.08/1.04  
% 3.08/1.04  --superposition_flag                    true
% 3.08/1.04  --sup_passive_queue_type                priority_queues
% 3.08/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.08/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.08/1.04  --demod_completeness_check              fast
% 3.08/1.04  --demod_use_ground                      true
% 3.08/1.04  --sup_to_prop_solver                    passive
% 3.08/1.04  --sup_prop_simpl_new                    true
% 3.08/1.04  --sup_prop_simpl_given                  true
% 3.08/1.04  --sup_fun_splitting                     false
% 3.08/1.04  --sup_smt_interval                      50000
% 3.08/1.04  
% 3.08/1.04  ------ Superposition Simplification Setup
% 3.08/1.04  
% 3.08/1.04  --sup_indices_passive                   []
% 3.08/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.08/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/1.04  --sup_full_bw                           [BwDemod]
% 3.08/1.04  --sup_immed_triv                        [TrivRules]
% 3.08/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.08/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/1.04  --sup_immed_bw_main                     []
% 3.08/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.08/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/1.04  
% 3.08/1.04  ------ Combination Options
% 3.08/1.04  
% 3.08/1.04  --comb_res_mult                         3
% 3.08/1.04  --comb_sup_mult                         2
% 3.08/1.04  --comb_inst_mult                        10
% 3.08/1.04  
% 3.08/1.04  ------ Debug Options
% 3.08/1.04  
% 3.08/1.04  --dbg_backtrace                         false
% 3.08/1.04  --dbg_dump_prop_clauses                 false
% 3.08/1.04  --dbg_dump_prop_clauses_file            -
% 3.08/1.04  --dbg_out_stat                          false
% 3.08/1.04  ------ Parsing...
% 3.08/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.08/1.04  
% 3.08/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.08/1.04  
% 3.08/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.08/1.04  
% 3.08/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.08/1.04  ------ Proving...
% 3.08/1.04  ------ Problem Properties 
% 3.08/1.04  
% 3.08/1.04  
% 3.08/1.04  clauses                                 20
% 3.08/1.04  conjectures                             5
% 3.08/1.04  EPR                                     5
% 3.08/1.04  Horn                                    19
% 3.08/1.04  unary                                   10
% 3.08/1.04  binary                                  2
% 3.08/1.04  lits                                    38
% 3.08/1.04  lits eq                                 6
% 3.08/1.04  fd_pure                                 0
% 3.08/1.04  fd_pseudo                               0
% 3.08/1.04  fd_cond                                 0
% 3.08/1.04  fd_pseudo_cond                          3
% 3.08/1.04  AC symbols                              0
% 3.08/1.04  
% 3.08/1.04  ------ Schedule dynamic 5 is on 
% 3.08/1.04  
% 3.08/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.08/1.04  
% 3.08/1.04  
% 3.08/1.04  ------ 
% 3.08/1.04  Current options:
% 3.08/1.04  ------ 
% 3.08/1.04  
% 3.08/1.04  ------ Input Options
% 3.08/1.04  
% 3.08/1.04  --out_options                           all
% 3.08/1.04  --tptp_safe_out                         true
% 3.08/1.04  --problem_path                          ""
% 3.08/1.04  --include_path                          ""
% 3.08/1.04  --clausifier                            res/vclausify_rel
% 3.08/1.04  --clausifier_options                    --mode clausify
% 3.08/1.04  --stdin                                 false
% 3.08/1.04  --stats_out                             all
% 3.08/1.04  
% 3.08/1.04  ------ General Options
% 3.08/1.04  
% 3.08/1.04  --fof                                   false
% 3.08/1.04  --time_out_real                         305.
% 3.08/1.04  --time_out_virtual                      -1.
% 3.08/1.04  --symbol_type_check                     false
% 3.08/1.04  --clausify_out                          false
% 3.08/1.04  --sig_cnt_out                           false
% 3.08/1.04  --trig_cnt_out                          false
% 3.08/1.04  --trig_cnt_out_tolerance                1.
% 3.08/1.04  --trig_cnt_out_sk_spl                   false
% 3.08/1.04  --abstr_cl_out                          false
% 3.08/1.04  
% 3.08/1.04  ------ Global Options
% 3.08/1.04  
% 3.08/1.04  --schedule                              default
% 3.08/1.04  --add_important_lit                     false
% 3.08/1.04  --prop_solver_per_cl                    1000
% 3.08/1.04  --min_unsat_core                        false
% 3.08/1.04  --soft_assumptions                      false
% 3.08/1.04  --soft_lemma_size                       3
% 3.08/1.04  --prop_impl_unit_size                   0
% 3.08/1.04  --prop_impl_unit                        []
% 3.08/1.04  --share_sel_clauses                     true
% 3.08/1.04  --reset_solvers                         false
% 3.08/1.04  --bc_imp_inh                            [conj_cone]
% 3.08/1.04  --conj_cone_tolerance                   3.
% 3.08/1.04  --extra_neg_conj                        none
% 3.08/1.04  --large_theory_mode                     true
% 3.08/1.04  --prolific_symb_bound                   200
% 3.08/1.04  --lt_threshold                          2000
% 3.08/1.04  --clause_weak_htbl                      true
% 3.08/1.04  --gc_record_bc_elim                     false
% 3.08/1.04  
% 3.08/1.04  ------ Preprocessing Options
% 3.08/1.04  
% 3.08/1.04  --preprocessing_flag                    true
% 3.08/1.04  --time_out_prep_mult                    0.1
% 3.08/1.04  --splitting_mode                        input
% 3.08/1.04  --splitting_grd                         true
% 3.08/1.04  --splitting_cvd                         false
% 3.08/1.04  --splitting_cvd_svl                     false
% 3.08/1.04  --splitting_nvd                         32
% 3.08/1.04  --sub_typing                            true
% 3.08/1.04  --prep_gs_sim                           true
% 3.08/1.04  --prep_unflatten                        true
% 3.08/1.04  --prep_res_sim                          true
% 3.08/1.04  --prep_upred                            true
% 3.08/1.04  --prep_sem_filter                       exhaustive
% 3.08/1.04  --prep_sem_filter_out                   false
% 3.08/1.04  --pred_elim                             true
% 3.08/1.04  --res_sim_input                         true
% 3.08/1.04  --eq_ax_congr_red                       true
% 3.08/1.04  --pure_diseq_elim                       true
% 3.08/1.04  --brand_transform                       false
% 3.08/1.04  --non_eq_to_eq                          false
% 3.08/1.04  --prep_def_merge                        true
% 3.08/1.04  --prep_def_merge_prop_impl              false
% 3.08/1.04  --prep_def_merge_mbd                    true
% 3.08/1.04  --prep_def_merge_tr_red                 false
% 3.08/1.04  --prep_def_merge_tr_cl                  false
% 3.08/1.04  --smt_preprocessing                     true
% 3.08/1.04  --smt_ac_axioms                         fast
% 3.08/1.04  --preprocessed_out                      false
% 3.08/1.04  --preprocessed_stats                    false
% 3.08/1.04  
% 3.08/1.04  ------ Abstraction refinement Options
% 3.08/1.04  
% 3.08/1.04  --abstr_ref                             []
% 3.08/1.04  --abstr_ref_prep                        false
% 3.08/1.04  --abstr_ref_until_sat                   false
% 3.08/1.04  --abstr_ref_sig_restrict                funpre
% 3.08/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.08/1.04  --abstr_ref_under                       []
% 3.08/1.04  
% 3.08/1.04  ------ SAT Options
% 3.08/1.04  
% 3.08/1.04  --sat_mode                              false
% 3.08/1.04  --sat_fm_restart_options                ""
% 3.08/1.04  --sat_gr_def                            false
% 3.08/1.04  --sat_epr_types                         true
% 3.08/1.04  --sat_non_cyclic_types                  false
% 3.08/1.04  --sat_finite_models                     false
% 3.08/1.04  --sat_fm_lemmas                         false
% 3.08/1.04  --sat_fm_prep                           false
% 3.08/1.04  --sat_fm_uc_incr                        true
% 3.08/1.04  --sat_out_model                         small
% 3.08/1.04  --sat_out_clauses                       false
% 3.08/1.04  
% 3.08/1.04  ------ QBF Options
% 3.08/1.04  
% 3.08/1.04  --qbf_mode                              false
% 3.08/1.04  --qbf_elim_univ                         false
% 3.08/1.04  --qbf_dom_inst                          none
% 3.08/1.04  --qbf_dom_pre_inst                      false
% 3.08/1.04  --qbf_sk_in                             false
% 3.08/1.04  --qbf_pred_elim                         true
% 3.08/1.04  --qbf_split                             512
% 3.08/1.04  
% 3.08/1.04  ------ BMC1 Options
% 3.08/1.04  
% 3.08/1.04  --bmc1_incremental                      false
% 3.08/1.04  --bmc1_axioms                           reachable_all
% 3.08/1.04  --bmc1_min_bound                        0
% 3.08/1.04  --bmc1_max_bound                        -1
% 3.08/1.04  --bmc1_max_bound_default                -1
% 3.08/1.04  --bmc1_symbol_reachability              true
% 3.08/1.04  --bmc1_property_lemmas                  false
% 3.08/1.04  --bmc1_k_induction                      false
% 3.08/1.04  --bmc1_non_equiv_states                 false
% 3.08/1.04  --bmc1_deadlock                         false
% 3.08/1.04  --bmc1_ucm                              false
% 3.08/1.04  --bmc1_add_unsat_core                   none
% 3.08/1.04  --bmc1_unsat_core_children              false
% 3.08/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.08/1.04  --bmc1_out_stat                         full
% 3.08/1.04  --bmc1_ground_init                      false
% 3.08/1.04  --bmc1_pre_inst_next_state              false
% 3.08/1.04  --bmc1_pre_inst_state                   false
% 3.08/1.04  --bmc1_pre_inst_reach_state             false
% 3.08/1.04  --bmc1_out_unsat_core                   false
% 3.08/1.04  --bmc1_aig_witness_out                  false
% 3.08/1.04  --bmc1_verbose                          false
% 3.08/1.04  --bmc1_dump_clauses_tptp                false
% 3.08/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.08/1.04  --bmc1_dump_file                        -
% 3.08/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.08/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.08/1.04  --bmc1_ucm_extend_mode                  1
% 3.08/1.04  --bmc1_ucm_init_mode                    2
% 3.08/1.04  --bmc1_ucm_cone_mode                    none
% 3.08/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.08/1.04  --bmc1_ucm_relax_model                  4
% 3.08/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.08/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.08/1.04  --bmc1_ucm_layered_model                none
% 3.08/1.04  --bmc1_ucm_max_lemma_size               10
% 3.08/1.04  
% 3.08/1.04  ------ AIG Options
% 3.08/1.04  
% 3.08/1.04  --aig_mode                              false
% 3.08/1.04  
% 3.08/1.04  ------ Instantiation Options
% 3.08/1.04  
% 3.08/1.04  --instantiation_flag                    true
% 3.08/1.04  --inst_sos_flag                         false
% 3.08/1.04  --inst_sos_phase                        true
% 3.08/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.08/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.08/1.04  --inst_lit_sel_side                     none
% 3.08/1.04  --inst_solver_per_active                1400
% 3.08/1.04  --inst_solver_calls_frac                1.
% 3.08/1.04  --inst_passive_queue_type               priority_queues
% 3.08/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.08/1.04  --inst_passive_queues_freq              [25;2]
% 3.08/1.04  --inst_dismatching                      true
% 3.08/1.04  --inst_eager_unprocessed_to_passive     true
% 3.08/1.04  --inst_prop_sim_given                   true
% 3.08/1.04  --inst_prop_sim_new                     false
% 3.08/1.04  --inst_subs_new                         false
% 3.08/1.04  --inst_eq_res_simp                      false
% 3.08/1.04  --inst_subs_given                       false
% 3.08/1.04  --inst_orphan_elimination               true
% 3.08/1.04  --inst_learning_loop_flag               true
% 3.08/1.04  --inst_learning_start                   3000
% 3.08/1.04  --inst_learning_factor                  2
% 3.08/1.04  --inst_start_prop_sim_after_learn       3
% 3.08/1.04  --inst_sel_renew                        solver
% 3.08/1.04  --inst_lit_activity_flag                true
% 3.08/1.04  --inst_restr_to_given                   false
% 3.08/1.04  --inst_activity_threshold               500
% 3.08/1.04  --inst_out_proof                        true
% 3.08/1.04  
% 3.08/1.04  ------ Resolution Options
% 3.08/1.04  
% 3.08/1.04  --resolution_flag                       false
% 3.08/1.04  --res_lit_sel                           adaptive
% 3.08/1.04  --res_lit_sel_side                      none
% 3.08/1.04  --res_ordering                          kbo
% 3.08/1.04  --res_to_prop_solver                    active
% 3.08/1.04  --res_prop_simpl_new                    false
% 3.08/1.04  --res_prop_simpl_given                  true
% 3.08/1.04  --res_passive_queue_type                priority_queues
% 3.08/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.08/1.04  --res_passive_queues_freq               [15;5]
% 3.08/1.04  --res_forward_subs                      full
% 3.08/1.04  --res_backward_subs                     full
% 3.08/1.04  --res_forward_subs_resolution           true
% 3.08/1.04  --res_backward_subs_resolution          true
% 3.08/1.04  --res_orphan_elimination                true
% 3.08/1.04  --res_time_limit                        2.
% 3.08/1.04  --res_out_proof                         true
% 3.08/1.04  
% 3.08/1.04  ------ Superposition Options
% 3.08/1.04  
% 3.08/1.04  --superposition_flag                    true
% 3.08/1.04  --sup_passive_queue_type                priority_queues
% 3.08/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.08/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.08/1.04  --demod_completeness_check              fast
% 3.08/1.04  --demod_use_ground                      true
% 3.08/1.04  --sup_to_prop_solver                    passive
% 3.08/1.04  --sup_prop_simpl_new                    true
% 3.08/1.04  --sup_prop_simpl_given                  true
% 3.08/1.04  --sup_fun_splitting                     false
% 3.08/1.04  --sup_smt_interval                      50000
% 3.08/1.04  
% 3.08/1.04  ------ Superposition Simplification Setup
% 3.08/1.04  
% 3.08/1.04  --sup_indices_passive                   []
% 3.08/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.08/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/1.04  --sup_full_bw                           [BwDemod]
% 3.08/1.04  --sup_immed_triv                        [TrivRules]
% 3.08/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.08/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/1.04  --sup_immed_bw_main                     []
% 3.08/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.08/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/1.04  
% 3.08/1.04  ------ Combination Options
% 3.08/1.04  
% 3.08/1.04  --comb_res_mult                         3
% 3.08/1.04  --comb_sup_mult                         2
% 3.08/1.04  --comb_inst_mult                        10
% 3.08/1.04  
% 3.08/1.04  ------ Debug Options
% 3.08/1.04  
% 3.08/1.04  --dbg_backtrace                         false
% 3.08/1.04  --dbg_dump_prop_clauses                 false
% 3.08/1.04  --dbg_dump_prop_clauses_file            -
% 3.08/1.04  --dbg_out_stat                          false
% 3.08/1.04  
% 3.08/1.04  
% 3.08/1.04  
% 3.08/1.04  
% 3.08/1.04  ------ Proving...
% 3.08/1.04  
% 3.08/1.04  
% 3.08/1.04  % SZS status Theorem for theBenchmark.p
% 3.08/1.04  
% 3.08/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.08/1.04  
% 3.08/1.04  fof(f11,conjecture,(
% 3.08/1.04    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 3.08/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.04  
% 3.08/1.04  fof(f12,negated_conjecture,(
% 3.08/1.04    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 3.08/1.04    inference(negated_conjecture,[],[f11])).
% 3.08/1.04  
% 3.08/1.04  fof(f27,plain,(
% 3.08/1.04    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.08/1.04    inference(ennf_transformation,[],[f12])).
% 3.08/1.04  
% 3.08/1.04  fof(f28,plain,(
% 3.08/1.04    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.08/1.04    inference(flattening,[],[f27])).
% 3.08/1.04  
% 3.08/1.04  fof(f35,plain,(
% 3.08/1.04    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK1,sK2) & v2_funct_1(sK3) & r1_tarski(sK1,k1_relat_1(sK3)) & r1_tarski(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 3.08/1.04    introduced(choice_axiom,[])).
% 3.08/1.04  
% 3.08/1.04  fof(f36,plain,(
% 3.08/1.04    ~r1_tarski(sK1,sK2) & v2_funct_1(sK3) & r1_tarski(sK1,k1_relat_1(sK3)) & r1_tarski(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 3.08/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f35])).
% 3.08/1.04  
% 3.08/1.04  fof(f56,plain,(
% 3.08/1.04    r1_tarski(sK1,k1_relat_1(sK3))),
% 3.08/1.04    inference(cnf_transformation,[],[f36])).
% 3.08/1.04  
% 3.08/1.04  fof(f8,axiom,(
% 3.08/1.04    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.08/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.04  
% 3.08/1.04  fof(f21,plain,(
% 3.08/1.04    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.08/1.04    inference(ennf_transformation,[],[f8])).
% 3.08/1.04  
% 3.08/1.04  fof(f22,plain,(
% 3.08/1.04    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.08/1.04    inference(flattening,[],[f21])).
% 3.08/1.04  
% 3.08/1.04  fof(f50,plain,(
% 3.08/1.04    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.08/1.04    inference(cnf_transformation,[],[f22])).
% 3.08/1.04  
% 3.08/1.04  fof(f9,axiom,(
% 3.08/1.04    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 3.08/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.04  
% 3.08/1.04  fof(f23,plain,(
% 3.08/1.04    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.08/1.04    inference(ennf_transformation,[],[f9])).
% 3.08/1.04  
% 3.08/1.04  fof(f24,plain,(
% 3.08/1.04    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.08/1.04    inference(flattening,[],[f23])).
% 3.08/1.04  
% 3.08/1.04  fof(f51,plain,(
% 3.08/1.04    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.08/1.04    inference(cnf_transformation,[],[f24])).
% 3.08/1.04  
% 3.08/1.04  fof(f57,plain,(
% 3.08/1.04    v2_funct_1(sK3)),
% 3.08/1.04    inference(cnf_transformation,[],[f36])).
% 3.08/1.04  
% 3.08/1.04  fof(f53,plain,(
% 3.08/1.04    v1_relat_1(sK3)),
% 3.08/1.04    inference(cnf_transformation,[],[f36])).
% 3.08/1.04  
% 3.08/1.04  fof(f54,plain,(
% 3.08/1.04    v1_funct_1(sK3)),
% 3.08/1.04    inference(cnf_transformation,[],[f36])).
% 3.08/1.04  
% 3.08/1.04  fof(f1,axiom,(
% 3.08/1.04    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.08/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.04  
% 3.08/1.04  fof(f29,plain,(
% 3.08/1.04    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.08/1.04    inference(nnf_transformation,[],[f1])).
% 3.08/1.04  
% 3.08/1.04  fof(f30,plain,(
% 3.08/1.04    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.08/1.04    inference(flattening,[],[f29])).
% 3.08/1.04  
% 3.08/1.04  fof(f39,plain,(
% 3.08/1.04    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.08/1.04    inference(cnf_transformation,[],[f30])).
% 3.08/1.04  
% 3.08/1.04  fof(f55,plain,(
% 3.08/1.04    r1_tarski(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))),
% 3.08/1.04    inference(cnf_transformation,[],[f36])).
% 3.08/1.04  
% 3.08/1.04  fof(f10,axiom,(
% 3.08/1.04    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 3.08/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.04  
% 3.08/1.04  fof(f25,plain,(
% 3.08/1.04    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.08/1.04    inference(ennf_transformation,[],[f10])).
% 3.08/1.04  
% 3.08/1.04  fof(f26,plain,(
% 3.08/1.04    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.08/1.04    inference(flattening,[],[f25])).
% 3.08/1.04  
% 3.08/1.04  fof(f52,plain,(
% 3.08/1.04    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.08/1.04    inference(cnf_transformation,[],[f26])).
% 3.08/1.04  
% 3.08/1.04  fof(f5,axiom,(
% 3.08/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.08/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.04  
% 3.08/1.04  fof(f15,plain,(
% 3.08/1.04    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 3.08/1.04    inference(ennf_transformation,[],[f5])).
% 3.08/1.04  
% 3.08/1.04  fof(f16,plain,(
% 3.08/1.04    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 3.08/1.04    inference(flattening,[],[f15])).
% 3.08/1.04  
% 3.08/1.04  fof(f46,plain,(
% 3.08/1.04    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 3.08/1.04    inference(cnf_transformation,[],[f16])).
% 3.08/1.04  
% 3.08/1.04  fof(f7,axiom,(
% 3.08/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.08/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.04  
% 3.08/1.04  fof(f19,plain,(
% 3.08/1.04    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.08/1.04    inference(ennf_transformation,[],[f7])).
% 3.08/1.04  
% 3.08/1.04  fof(f20,plain,(
% 3.08/1.04    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.08/1.04    inference(flattening,[],[f19])).
% 3.08/1.04  
% 3.08/1.04  fof(f48,plain,(
% 3.08/1.04    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.08/1.04    inference(cnf_transformation,[],[f20])).
% 3.08/1.04  
% 3.08/1.04  fof(f2,axiom,(
% 3.08/1.04    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.08/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.04  
% 3.08/1.04  fof(f31,plain,(
% 3.08/1.04    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.08/1.04    inference(nnf_transformation,[],[f2])).
% 3.08/1.04  
% 3.08/1.04  fof(f32,plain,(
% 3.08/1.04    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.08/1.04    inference(rectify,[],[f31])).
% 3.08/1.04  
% 3.08/1.04  fof(f33,plain,(
% 3.08/1.04    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.08/1.04    introduced(choice_axiom,[])).
% 3.08/1.04  
% 3.08/1.04  fof(f34,plain,(
% 3.08/1.04    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.08/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 3.08/1.04  
% 3.08/1.04  fof(f41,plain,(
% 3.08/1.04    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.08/1.04    inference(cnf_transformation,[],[f34])).
% 3.08/1.04  
% 3.08/1.04  fof(f61,plain,(
% 3.08/1.04    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.08/1.04    inference(equality_resolution,[],[f41])).
% 3.08/1.04  
% 3.08/1.04  fof(f3,axiom,(
% 3.08/1.04    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 3.08/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.04  
% 3.08/1.04  fof(f44,plain,(
% 3.08/1.04    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 3.08/1.04    inference(cnf_transformation,[],[f3])).
% 3.08/1.04  
% 3.08/1.04  fof(f4,axiom,(
% 3.08/1.04    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 3.08/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.04  
% 3.08/1.04  fof(f13,plain,(
% 3.08/1.04    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 3.08/1.04    inference(ennf_transformation,[],[f4])).
% 3.08/1.04  
% 3.08/1.04  fof(f14,plain,(
% 3.08/1.04    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 3.08/1.04    inference(flattening,[],[f13])).
% 3.08/1.04  
% 3.08/1.04  fof(f45,plain,(
% 3.08/1.04    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)) )),
% 3.08/1.04    inference(cnf_transformation,[],[f14])).
% 3.08/1.04  
% 3.08/1.04  fof(f58,plain,(
% 3.08/1.04    ~r1_tarski(sK1,sK2)),
% 3.08/1.04    inference(cnf_transformation,[],[f36])).
% 3.08/1.04  
% 3.08/1.04  cnf(c_18,negated_conjecture,
% 3.08/1.04      ( r1_tarski(sK1,k1_relat_1(sK3)) ),
% 3.08/1.04      inference(cnf_transformation,[],[f56]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_1048,plain,
% 3.08/1.04      ( r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top ),
% 3.08/1.04      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_13,plain,
% 3.08/1.04      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 3.08/1.04      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.08/1.04      | ~ v1_relat_1(X1) ),
% 3.08/1.04      inference(cnf_transformation,[],[f50]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_1050,plain,
% 3.08/1.04      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 3.08/1.04      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 3.08/1.04      | v1_relat_1(X1) != iProver_top ),
% 3.08/1.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_14,plain,
% 3.08/1.04      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 3.08/1.04      | ~ v1_funct_1(X0)
% 3.08/1.04      | ~ v2_funct_1(X0)
% 3.08/1.04      | ~ v1_relat_1(X0) ),
% 3.08/1.04      inference(cnf_transformation,[],[f51]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_17,negated_conjecture,
% 3.08/1.04      ( v2_funct_1(sK3) ),
% 3.08/1.04      inference(cnf_transformation,[],[f57]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_281,plain,
% 3.08/1.04      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 3.08/1.04      | ~ v1_funct_1(X0)
% 3.08/1.04      | ~ v1_relat_1(X0)
% 3.08/1.04      | sK3 != X0 ),
% 3.08/1.04      inference(resolution_lifted,[status(thm)],[c_14,c_17]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_282,plain,
% 3.08/1.04      ( r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,X0)),X0)
% 3.08/1.04      | ~ v1_funct_1(sK3)
% 3.08/1.04      | ~ v1_relat_1(sK3) ),
% 3.08/1.04      inference(unflattening,[status(thm)],[c_281]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_21,negated_conjecture,
% 3.08/1.04      ( v1_relat_1(sK3) ),
% 3.08/1.04      inference(cnf_transformation,[],[f53]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_20,negated_conjecture,
% 3.08/1.04      ( v1_funct_1(sK3) ),
% 3.08/1.04      inference(cnf_transformation,[],[f54]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_286,plain,
% 3.08/1.04      ( r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,X0)),X0) ),
% 3.08/1.04      inference(global_propositional_subsumption,
% 3.08/1.04                [status(thm)],
% 3.08/1.04                [c_282,c_21,c_20]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_1044,plain,
% 3.08/1.04      ( r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,X0)),X0) = iProver_top ),
% 3.08/1.04      inference(predicate_to_equality,[status(thm)],[c_286]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_0,plain,
% 3.08/1.04      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.08/1.04      inference(cnf_transformation,[],[f39]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_1060,plain,
% 3.08/1.04      ( X0 = X1
% 3.08/1.04      | r1_tarski(X0,X1) != iProver_top
% 3.08/1.04      | r1_tarski(X1,X0) != iProver_top ),
% 3.08/1.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_1799,plain,
% 3.08/1.04      ( k10_relat_1(sK3,k9_relat_1(sK3,X0)) = X0
% 3.08/1.04      | r1_tarski(X0,k10_relat_1(sK3,k9_relat_1(sK3,X0))) != iProver_top ),
% 3.08/1.04      inference(superposition,[status(thm)],[c_1044,c_1060]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_1962,plain,
% 3.08/1.04      ( k10_relat_1(sK3,k9_relat_1(sK3,X0)) = X0
% 3.08/1.04      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 3.08/1.04      | v1_relat_1(sK3) != iProver_top ),
% 3.08/1.04      inference(superposition,[status(thm)],[c_1050,c_1799]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_22,plain,
% 3.08/1.04      ( v1_relat_1(sK3) = iProver_top ),
% 3.08/1.04      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_6099,plain,
% 3.08/1.04      ( r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 3.08/1.04      | k10_relat_1(sK3,k9_relat_1(sK3,X0)) = X0 ),
% 3.08/1.04      inference(global_propositional_subsumption,
% 3.08/1.04                [status(thm)],
% 3.08/1.04                [c_1962,c_22]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_6100,plain,
% 3.08/1.04      ( k10_relat_1(sK3,k9_relat_1(sK3,X0)) = X0
% 3.08/1.04      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
% 3.08/1.04      inference(renaming,[status(thm)],[c_6099]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_6109,plain,
% 3.08/1.04      ( k10_relat_1(sK3,k9_relat_1(sK3,sK1)) = sK1 ),
% 3.08/1.04      inference(superposition,[status(thm)],[c_1048,c_6100]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_19,negated_conjecture,
% 3.08/1.04      ( r1_tarski(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)) ),
% 3.08/1.04      inference(cnf_transformation,[],[f55]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_1047,plain,
% 3.08/1.04      ( r1_tarski(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)) = iProver_top ),
% 3.08/1.04      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_15,plain,
% 3.08/1.04      ( ~ v1_funct_1(X0)
% 3.08/1.04      | ~ v2_funct_1(X0)
% 3.08/1.04      | ~ v1_relat_1(X0)
% 3.08/1.04      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 3.08/1.04      inference(cnf_transformation,[],[f52]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_270,plain,
% 3.08/1.04      ( ~ v1_funct_1(X0)
% 3.08/1.04      | ~ v1_relat_1(X0)
% 3.08/1.04      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 3.08/1.04      | sK3 != X0 ),
% 3.08/1.04      inference(resolution_lifted,[status(thm)],[c_15,c_17]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_271,plain,
% 3.08/1.04      ( ~ v1_funct_1(sK3)
% 3.08/1.04      | ~ v1_relat_1(sK3)
% 3.08/1.04      | k9_relat_1(k2_funct_1(sK3),X0) = k10_relat_1(sK3,X0) ),
% 3.08/1.04      inference(unflattening,[status(thm)],[c_270]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_275,plain,
% 3.08/1.04      ( k9_relat_1(k2_funct_1(sK3),X0) = k10_relat_1(sK3,X0) ),
% 3.08/1.04      inference(global_propositional_subsumption,
% 3.08/1.04                [status(thm)],
% 3.08/1.04                [c_271,c_21,c_20]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_9,plain,
% 3.08/1.04      ( ~ r1_tarski(X0,X1)
% 3.08/1.04      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 3.08/1.04      | ~ v1_relat_1(X2) ),
% 3.08/1.04      inference(cnf_transformation,[],[f46]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_1053,plain,
% 3.08/1.04      ( r1_tarski(X0,X1) != iProver_top
% 3.08/1.04      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
% 3.08/1.04      | v1_relat_1(X2) != iProver_top ),
% 3.08/1.04      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_2033,plain,
% 3.08/1.04      ( r1_tarski(X0,X1) != iProver_top
% 3.08/1.04      | r1_tarski(k9_relat_1(k2_funct_1(sK3),X0),k10_relat_1(sK3,X1)) = iProver_top
% 3.08/1.04      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.08/1.04      inference(superposition,[status(thm)],[c_275,c_1053]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_2053,plain,
% 3.08/1.04      ( r1_tarski(X0,X1) != iProver_top
% 3.08/1.04      | r1_tarski(k10_relat_1(sK3,X0),k10_relat_1(sK3,X1)) = iProver_top
% 3.08/1.04      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.08/1.04      inference(light_normalisation,[status(thm)],[c_2033,c_275]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_23,plain,
% 3.08/1.04      ( v1_funct_1(sK3) = iProver_top ),
% 3.08/1.04      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_12,plain,
% 3.08/1.04      ( ~ v1_funct_1(X0)
% 3.08/1.04      | ~ v1_relat_1(X0)
% 3.08/1.04      | v1_relat_1(k2_funct_1(X0)) ),
% 3.08/1.04      inference(cnf_transformation,[],[f48]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_37,plain,
% 3.08/1.04      ( v1_funct_1(X0) != iProver_top
% 3.08/1.04      | v1_relat_1(X0) != iProver_top
% 3.08/1.04      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.08/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_39,plain,
% 3.08/1.04      ( v1_funct_1(sK3) != iProver_top
% 3.08/1.04      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 3.08/1.04      | v1_relat_1(sK3) != iProver_top ),
% 3.08/1.04      inference(instantiation,[status(thm)],[c_37]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_2389,plain,
% 3.08/1.04      ( r1_tarski(k10_relat_1(sK3,X0),k10_relat_1(sK3,X1)) = iProver_top
% 3.08/1.04      | r1_tarski(X0,X1) != iProver_top ),
% 3.08/1.04      inference(global_propositional_subsumption,
% 3.08/1.04                [status(thm)],
% 3.08/1.04                [c_2053,c_22,c_23,c_39]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_2390,plain,
% 3.08/1.04      ( r1_tarski(X0,X1) != iProver_top
% 3.08/1.04      | r1_tarski(k10_relat_1(sK3,X0),k10_relat_1(sK3,X1)) = iProver_top ),
% 3.08/1.04      inference(renaming,[status(thm)],[c_2389]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_5,plain,
% 3.08/1.04      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.08/1.04      inference(cnf_transformation,[],[f61]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_1056,plain,
% 3.08/1.04      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.08/1.04      | r1_tarski(X0,X1) != iProver_top ),
% 3.08/1.04      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_7,plain,
% 3.08/1.04      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 3.08/1.04      inference(cnf_transformation,[],[f44]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_8,plain,
% 3.08/1.04      ( ~ r2_hidden(X0,X1)
% 3.08/1.04      | r1_tarski(X0,X2)
% 3.08/1.04      | ~ r1_tarski(k3_tarski(X1),X2) ),
% 3.08/1.04      inference(cnf_transformation,[],[f45]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_1054,plain,
% 3.08/1.04      ( r2_hidden(X0,X1) != iProver_top
% 3.08/1.04      | r1_tarski(X0,X2) = iProver_top
% 3.08/1.04      | r1_tarski(k3_tarski(X1),X2) != iProver_top ),
% 3.08/1.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_2075,plain,
% 3.08/1.04      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.08/1.04      | r1_tarski(X1,X2) != iProver_top
% 3.08/1.04      | r1_tarski(X0,X2) = iProver_top ),
% 3.08/1.04      inference(superposition,[status(thm)],[c_7,c_1054]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_2257,plain,
% 3.08/1.04      ( r1_tarski(X0,X1) != iProver_top
% 3.08/1.04      | r1_tarski(X1,X2) != iProver_top
% 3.08/1.04      | r1_tarski(X0,X2) = iProver_top ),
% 3.08/1.04      inference(superposition,[status(thm)],[c_1056,c_2075]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_3226,plain,
% 3.08/1.04      ( r1_tarski(X0,X1) != iProver_top
% 3.08/1.04      | r1_tarski(k10_relat_1(sK3,X1),X2) != iProver_top
% 3.08/1.04      | r1_tarski(k10_relat_1(sK3,X0),X2) = iProver_top ),
% 3.08/1.04      inference(superposition,[status(thm)],[c_2390,c_2257]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_4055,plain,
% 3.08/1.04      ( r1_tarski(X0,k9_relat_1(sK3,X1)) != iProver_top
% 3.08/1.04      | r1_tarski(k10_relat_1(sK3,X0),X1) = iProver_top ),
% 3.08/1.04      inference(superposition,[status(thm)],[c_1044,c_3226]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_4225,plain,
% 3.08/1.04      ( r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,sK1)),sK2) = iProver_top ),
% 3.08/1.04      inference(superposition,[status(thm)],[c_1047,c_4055]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_6246,plain,
% 3.08/1.04      ( r1_tarski(sK1,sK2) = iProver_top ),
% 3.08/1.04      inference(demodulation,[status(thm)],[c_6109,c_4225]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_16,negated_conjecture,
% 3.08/1.04      ( ~ r1_tarski(sK1,sK2) ),
% 3.08/1.04      inference(cnf_transformation,[],[f58]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(c_27,plain,
% 3.08/1.04      ( r1_tarski(sK1,sK2) != iProver_top ),
% 3.08/1.04      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.08/1.04  
% 3.08/1.04  cnf(contradiction,plain,
% 3.08/1.04      ( $false ),
% 3.08/1.04      inference(minisat,[status(thm)],[c_6246,c_27]) ).
% 3.08/1.04  
% 3.08/1.04  
% 3.08/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 3.08/1.04  
% 3.08/1.04  ------                               Statistics
% 3.08/1.04  
% 3.08/1.04  ------ General
% 3.08/1.04  
% 3.08/1.04  abstr_ref_over_cycles:                  0
% 3.08/1.04  abstr_ref_under_cycles:                 0
% 3.08/1.04  gc_basic_clause_elim:                   0
% 3.08/1.04  forced_gc_time:                         0
% 3.08/1.04  parsing_time:                           0.046
% 3.08/1.04  unif_index_cands_time:                  0.
% 3.08/1.04  unif_index_add_time:                    0.
% 3.08/1.04  orderings_time:                         0.
% 3.08/1.04  out_proof_time:                         0.009
% 3.08/1.04  total_time:                             0.235
% 3.08/1.04  num_of_symbols:                         47
% 3.08/1.04  num_of_terms:                           6381
% 3.08/1.04  
% 3.08/1.04  ------ Preprocessing
% 3.08/1.04  
% 3.08/1.04  num_of_splits:                          0
% 3.08/1.04  num_of_split_atoms:                     0
% 3.08/1.04  num_of_reused_defs:                     0
% 3.08/1.04  num_eq_ax_congr_red:                    12
% 3.08/1.04  num_of_sem_filtered_clauses:            1
% 3.08/1.04  num_of_subtypes:                        0
% 3.08/1.04  monotx_restored_types:                  0
% 3.08/1.04  sat_num_of_epr_types:                   0
% 3.08/1.04  sat_num_of_non_cyclic_types:            0
% 3.08/1.04  sat_guarded_non_collapsed_types:        0
% 3.08/1.04  num_pure_diseq_elim:                    0
% 3.08/1.04  simp_replaced_by:                       0
% 3.08/1.04  res_preprocessed:                       106
% 3.08/1.04  prep_upred:                             0
% 3.08/1.04  prep_unflattend:                        19
% 3.08/1.04  smt_new_axioms:                         0
% 3.08/1.04  pred_elim_cands:                        4
% 3.08/1.04  pred_elim:                              1
% 3.08/1.04  pred_elim_cl:                           1
% 3.08/1.04  pred_elim_cycles:                       3
% 3.08/1.04  merged_defs:                            8
% 3.08/1.04  merged_defs_ncl:                        0
% 3.08/1.04  bin_hyper_res:                          8
% 3.08/1.04  prep_cycles:                            4
% 3.08/1.04  pred_elim_time:                         0.004
% 3.08/1.04  splitting_time:                         0.
% 3.08/1.04  sem_filter_time:                        0.
% 3.08/1.04  monotx_time:                            0.
% 3.08/1.04  subtype_inf_time:                       0.
% 3.08/1.04  
% 3.08/1.04  ------ Problem properties
% 3.08/1.04  
% 3.08/1.04  clauses:                                20
% 3.08/1.04  conjectures:                            5
% 3.08/1.04  epr:                                    5
% 3.08/1.04  horn:                                   19
% 3.08/1.04  ground:                                 6
% 3.08/1.04  unary:                                  10
% 3.08/1.04  binary:                                 2
% 3.08/1.04  lits:                                   38
% 3.08/1.04  lits_eq:                                6
% 3.08/1.04  fd_pure:                                0
% 3.08/1.04  fd_pseudo:                              0
% 3.08/1.04  fd_cond:                                0
% 3.08/1.04  fd_pseudo_cond:                         3
% 3.08/1.04  ac_symbols:                             0
% 3.08/1.04  
% 3.08/1.04  ------ Propositional Solver
% 3.08/1.04  
% 3.08/1.04  prop_solver_calls:                      30
% 3.08/1.04  prop_fast_solver_calls:                 635
% 3.08/1.04  smt_solver_calls:                       0
% 3.08/1.04  smt_fast_solver_calls:                  0
% 3.08/1.04  prop_num_of_clauses:                    2534
% 3.08/1.04  prop_preprocess_simplified:             6353
% 3.08/1.04  prop_fo_subsumed:                       11
% 3.08/1.04  prop_solver_time:                       0.
% 3.08/1.04  smt_solver_time:                        0.
% 3.08/1.04  smt_fast_solver_time:                   0.
% 3.08/1.04  prop_fast_solver_time:                  0.
% 3.08/1.04  prop_unsat_core_time:                   0.
% 3.08/1.04  
% 3.08/1.04  ------ QBF
% 3.08/1.04  
% 3.08/1.04  qbf_q_res:                              0
% 3.08/1.04  qbf_num_tautologies:                    0
% 3.08/1.04  qbf_prep_cycles:                        0
% 3.08/1.04  
% 3.08/1.04  ------ BMC1
% 3.08/1.04  
% 3.08/1.04  bmc1_current_bound:                     -1
% 3.08/1.04  bmc1_last_solved_bound:                 -1
% 3.08/1.04  bmc1_unsat_core_size:                   -1
% 3.08/1.04  bmc1_unsat_core_parents_size:           -1
% 3.08/1.04  bmc1_merge_next_fun:                    0
% 3.08/1.04  bmc1_unsat_core_clauses_time:           0.
% 3.08/1.04  
% 3.08/1.04  ------ Instantiation
% 3.08/1.04  
% 3.08/1.04  inst_num_of_clauses:                    668
% 3.08/1.04  inst_num_in_passive:                    294
% 3.08/1.04  inst_num_in_active:                     298
% 3.08/1.04  inst_num_in_unprocessed:                76
% 3.08/1.04  inst_num_of_loops:                      310
% 3.08/1.04  inst_num_of_learning_restarts:          0
% 3.08/1.04  inst_num_moves_active_passive:          8
% 3.08/1.04  inst_lit_activity:                      0
% 3.08/1.04  inst_lit_activity_moves:                0
% 3.08/1.04  inst_num_tautologies:                   0
% 3.08/1.04  inst_num_prop_implied:                  0
% 3.08/1.04  inst_num_existing_simplified:           0
% 3.08/1.04  inst_num_eq_res_simplified:             0
% 3.08/1.04  inst_num_child_elim:                    0
% 3.08/1.04  inst_num_of_dismatching_blockings:      227
% 3.08/1.04  inst_num_of_non_proper_insts:           691
% 3.08/1.04  inst_num_of_duplicates:                 0
% 3.08/1.04  inst_inst_num_from_inst_to_res:         0
% 3.08/1.04  inst_dismatching_checking_time:         0.
% 3.08/1.04  
% 3.08/1.04  ------ Resolution
% 3.08/1.04  
% 3.08/1.04  res_num_of_clauses:                     0
% 3.08/1.04  res_num_in_passive:                     0
% 3.08/1.04  res_num_in_active:                      0
% 3.08/1.04  res_num_of_loops:                       110
% 3.08/1.04  res_forward_subset_subsumed:            49
% 3.08/1.04  res_backward_subset_subsumed:           0
% 3.08/1.04  res_forward_subsumed:                   0
% 3.08/1.04  res_backward_subsumed:                  0
% 3.08/1.04  res_forward_subsumption_resolution:     0
% 3.08/1.04  res_backward_subsumption_resolution:    0
% 3.08/1.04  res_clause_to_clause_subsumption:       760
% 3.08/1.04  res_orphan_elimination:                 0
% 3.08/1.04  res_tautology_del:                      49
% 3.08/1.04  res_num_eq_res_simplified:              0
% 3.08/1.04  res_num_sel_changes:                    0
% 3.08/1.04  res_moves_from_active_to_pass:          0
% 3.08/1.04  
% 3.08/1.04  ------ Superposition
% 3.08/1.04  
% 3.08/1.04  sup_time_total:                         0.
% 3.08/1.04  sup_time_generating:                    0.
% 3.08/1.04  sup_time_sim_full:                      0.
% 3.08/1.04  sup_time_sim_immed:                     0.
% 3.08/1.04  
% 3.08/1.04  sup_num_of_clauses:                     168
% 3.08/1.04  sup_num_in_active:                      56
% 3.08/1.04  sup_num_in_passive:                     112
% 3.08/1.04  sup_num_of_loops:                       60
% 3.08/1.04  sup_fw_superposition:                   121
% 3.08/1.04  sup_bw_superposition:                   57
% 3.08/1.04  sup_immediate_simplified:               11
% 3.08/1.04  sup_given_eliminated:                   0
% 3.08/1.04  comparisons_done:                       0
% 3.08/1.04  comparisons_avoided:                    0
% 3.08/1.04  
% 3.08/1.04  ------ Simplifications
% 3.08/1.04  
% 3.08/1.04  
% 3.08/1.04  sim_fw_subset_subsumed:                 3
% 3.08/1.04  sim_bw_subset_subsumed:                 0
% 3.08/1.04  sim_fw_subsumed:                        2
% 3.08/1.04  sim_bw_subsumed:                        0
% 3.08/1.04  sim_fw_subsumption_res:                 0
% 3.08/1.04  sim_bw_subsumption_res:                 0
% 3.08/1.04  sim_tautology_del:                      2
% 3.08/1.04  sim_eq_tautology_del:                   4
% 3.08/1.04  sim_eq_res_simp:                        0
% 3.08/1.04  sim_fw_demodulated:                     2
% 3.08/1.04  sim_bw_demodulated:                     5
% 3.08/1.04  sim_light_normalised:                   3
% 3.08/1.04  sim_joinable_taut:                      0
% 3.08/1.04  sim_joinable_simp:                      0
% 3.08/1.04  sim_ac_normalised:                      0
% 3.08/1.04  sim_smt_subsumption:                    0
% 3.08/1.04  
%------------------------------------------------------------------------------

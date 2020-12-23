%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0640+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:47 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 433 expanded)
%              Number of clauses        :   75 ( 121 expanded)
%              Number of leaves         :    9 ( 107 expanded)
%              Depth                    :   20
%              Number of atoms          :  476 (2661 expanded)
%              Number of equality atoms :  186 ( 350 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                & v2_funct_1(k5_relat_1(X1,X0)) )
             => v2_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          & v2_funct_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          & v2_funct_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          & v2_funct_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ~ v2_funct_1(sK3)
        & r1_tarski(k2_relat_1(sK3),k1_relat_1(X0))
        & v2_funct_1(k5_relat_1(sK3,X0))
        & v1_funct_1(sK3)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_funct_1(X1)
            & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
            & v2_funct_1(k5_relat_1(X1,X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X1),k1_relat_1(sK2))
          & v2_funct_1(k5_relat_1(X1,sK2))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ v2_funct_1(sK3)
    & r1_tarski(k2_relat_1(sK3),k1_relat_1(sK2))
    & v2_funct_1(k5_relat_1(sK3,sK2))
    & v1_funct_1(sK3)
    & v1_relat_1(sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f25,f24])).

fof(f39,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK0(X0) != sK1(X0)
        & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
        & r2_hidden(sK1(X0),k1_relat_1(X0))
        & r2_hidden(sK0(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK0(X0) != sK1(X0)
            & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
            & r2_hidden(sK1(X0),k1_relat_1(X0))
            & r2_hidden(sK0(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f29,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f30,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f27,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    v2_funct_1(k5_relat_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_757,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1056,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_755,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1058,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_2,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_768,plain,
    ( r2_hidden(sK1(X0_41),k1_relat_1(X0_41))
    | ~ v1_relat_1(X0_41)
    | ~ v1_funct_1(X0_41)
    | v2_funct_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1045,plain,
    ( r2_hidden(sK1(X0_41),k1_relat_1(X0_41)) = iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v2_funct_1(X0_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_768])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_763,plain,
    ( ~ r2_hidden(X0_44,k1_relat_1(X0_41))
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | ~ v1_funct_1(X1_41)
    | ~ v1_funct_1(X0_41)
    | k1_funct_1(k5_relat_1(X0_41,X1_41),X0_44) = k1_funct_1(X1_41,k1_funct_1(X0_41,X0_44)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1050,plain,
    ( k1_funct_1(k5_relat_1(X0_41,X1_41),X0_44) = k1_funct_1(X1_41,k1_funct_1(X0_41,X0_44))
    | r2_hidden(X0_44,k1_relat_1(X0_41)) != iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(X1_41) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v1_funct_1(X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_1749,plain,
    ( k1_funct_1(X0_41,k1_funct_1(X1_41,sK1(X1_41))) = k1_funct_1(k5_relat_1(X1_41,X0_41),sK1(X1_41))
    | v1_relat_1(X1_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | v1_funct_1(X1_41) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v2_funct_1(X1_41) = iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_1050])).

cnf(c_2644,plain,
    ( k1_funct_1(k5_relat_1(X0_41,sK2),sK1(X0_41)) = k1_funct_1(sK2,k1_funct_1(X0_41,sK1(X0_41)))
    | v1_relat_1(X0_41) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X0_41) = iProver_top ),
    inference(superposition,[status(thm)],[c_1058,c_1749])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2916,plain,
    ( v1_funct_1(X0_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | k1_funct_1(k5_relat_1(X0_41,sK2),sK1(X0_41)) = k1_funct_1(sK2,k1_funct_1(X0_41,sK1(X0_41)))
    | v2_funct_1(X0_41) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2644,c_18])).

cnf(c_2917,plain,
    ( k1_funct_1(k5_relat_1(X0_41,sK2),sK1(X0_41)) = k1_funct_1(sK2,k1_funct_1(X0_41,sK1(X0_41)))
    | v1_relat_1(X0_41) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v2_funct_1(X0_41) = iProver_top ),
    inference(renaming,[status(thm)],[c_2916])).

cnf(c_2926,plain,
    ( k1_funct_1(sK2,k1_funct_1(sK3,sK1(sK3))) = k1_funct_1(k5_relat_1(sK3,sK2),sK1(sK3))
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_2917])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_769,plain,
    ( ~ v1_relat_1(X0_41)
    | ~ v1_funct_1(X0_41)
    | v2_funct_1(X0_41)
    | k1_funct_1(X0_41,sK1(X0_41)) = k1_funct_1(X0_41,sK0(X0_41)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1044,plain,
    ( k1_funct_1(X0_41,sK1(X0_41)) = k1_funct_1(X0_41,sK0(X0_41))
    | v1_relat_1(X0_41) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v2_funct_1(X0_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_769])).

cnf(c_1384,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1044])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_20,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,negated_conjecture,
    ( ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_23,plain,
    ( v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1577,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1384,c_20,c_23])).

cnf(c_2948,plain,
    ( k1_funct_1(sK2,k1_funct_1(sK3,sK0(sK3))) = k1_funct_1(k5_relat_1(sK3,sK2),sK1(sK3))
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2926,c_1577])).

cnf(c_3619,plain,
    ( k1_funct_1(sK2,k1_funct_1(sK3,sK0(sK3))) = k1_funct_1(k5_relat_1(sK3,sK2),sK1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2948,c_20,c_23])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_767,plain,
    ( r2_hidden(sK0(X0_41),k1_relat_1(X0_41))
    | ~ v1_relat_1(X0_41)
    | ~ v1_funct_1(X0_41)
    | v2_funct_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1046,plain,
    ( r2_hidden(sK0(X0_41),k1_relat_1(X0_41)) = iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v2_funct_1(X0_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_767])).

cnf(c_1748,plain,
    ( k1_funct_1(X0_41,k1_funct_1(X1_41,sK0(X1_41))) = k1_funct_1(k5_relat_1(X1_41,X0_41),sK0(X1_41))
    | v1_relat_1(X1_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | v1_funct_1(X1_41) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v2_funct_1(X1_41) = iProver_top ),
    inference(superposition,[status(thm)],[c_1046,c_1050])).

cnf(c_2097,plain,
    ( k1_funct_1(k5_relat_1(X0_41,sK2),sK0(X0_41)) = k1_funct_1(sK2,k1_funct_1(X0_41,sK0(X0_41)))
    | v1_relat_1(X0_41) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X0_41) = iProver_top ),
    inference(superposition,[status(thm)],[c_1058,c_1748])).

cnf(c_2314,plain,
    ( v1_funct_1(X0_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | k1_funct_1(k5_relat_1(X0_41,sK2),sK0(X0_41)) = k1_funct_1(sK2,k1_funct_1(X0_41,sK0(X0_41)))
    | v2_funct_1(X0_41) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2097,c_18])).

cnf(c_2315,plain,
    ( k1_funct_1(k5_relat_1(X0_41,sK2),sK0(X0_41)) = k1_funct_1(sK2,k1_funct_1(X0_41,sK0(X0_41)))
    | v1_relat_1(X0_41) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v2_funct_1(X0_41) = iProver_top ),
    inference(renaming,[status(thm)],[c_2314])).

cnf(c_2324,plain,
    ( k1_funct_1(sK2,k1_funct_1(sK3,sK0(sK3))) = k1_funct_1(k5_relat_1(sK3,sK2),sK0(sK3))
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_2315])).

cnf(c_2410,plain,
    ( k1_funct_1(sK2,k1_funct_1(sK3,sK0(sK3))) = k1_funct_1(k5_relat_1(sK3,sK2),sK0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2324,c_20,c_23])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_766,plain,
    ( ~ r2_hidden(X0_44,k1_relat_1(X0_41))
    | ~ r2_hidden(X1_44,k1_relat_1(X0_41))
    | ~ v1_relat_1(X0_41)
    | ~ v1_funct_1(X0_41)
    | ~ v2_funct_1(X0_41)
    | X0_44 = X1_44
    | k1_funct_1(X0_41,X0_44) != k1_funct_1(X0_41,X1_44) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1047,plain,
    ( X0_44 = X1_44
    | k1_funct_1(X0_41,X0_44) != k1_funct_1(X0_41,X1_44)
    | r2_hidden(X0_44,k1_relat_1(X0_41)) != iProver_top
    | r2_hidden(X1_44,k1_relat_1(X0_41)) != iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v2_funct_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_2439,plain,
    ( k1_funct_1(sK2,k1_funct_1(sK3,sK0(sK3))) != k1_funct_1(k5_relat_1(sK3,sK2),X0_44)
    | sK0(sK3) = X0_44
    | r2_hidden(X0_44,k1_relat_1(k5_relat_1(sK3,sK2))) != iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(k5_relat_1(sK3,sK2))) != iProver_top
    | v1_relat_1(k5_relat_1(sK3,sK2)) != iProver_top
    | v1_funct_1(k5_relat_1(sK3,sK2)) != iProver_top
    | v2_funct_1(k5_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2410,c_1047])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_760,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1053,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_760])).

cnf(c_9,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_762,plain,
    ( ~ r1_tarski(k2_relat_1(X0_41),k1_relat_1(X1_41))
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | k1_relat_1(k5_relat_1(X0_41,X1_41)) = k1_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1051,plain,
    ( k1_relat_1(k5_relat_1(X0_41,X1_41)) = k1_relat_1(X0_41)
    | r1_tarski(k2_relat_1(X0_41),k1_relat_1(X1_41)) != iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_762])).

cnf(c_1497,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK2)) = k1_relat_1(sK3)
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_1051])).

cnf(c_1198,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k5_relat_1(sK3,sK2)) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_1500,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK2)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1497,c_16,c_14,c_11,c_1198])).

cnf(c_2441,plain,
    ( k1_funct_1(sK2,k1_funct_1(sK3,sK0(sK3))) != k1_funct_1(k5_relat_1(sK3,sK2),X0_44)
    | sK0(sK3) = X0_44
    | r2_hidden(X0_44,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(k5_relat_1(sK3,sK2)) != iProver_top
    | v1_funct_1(k5_relat_1(sK3,sK2)) != iProver_top
    | v2_funct_1(k5_relat_1(sK3,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2439,c_1500])).

cnf(c_17,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_19,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,negated_conjecture,
    ( v2_funct_1(k5_relat_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_21,plain,
    ( v2_funct_1(k5_relat_1(sK3,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_40,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_42,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_765,plain,
    ( ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | v1_relat_1(k5_relat_1(X0_41,X1_41)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1277,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_1278,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1277])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v1_funct_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_764,plain,
    ( ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | ~ v1_funct_1(X1_41)
    | ~ v1_funct_1(X0_41)
    | v1_funct_1(k5_relat_1(X0_41,X1_41)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1288,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | v1_funct_1(k5_relat_1(sK3,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_764])).

cnf(c_1289,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(k5_relat_1(sK3,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1288])).

cnf(c_3112,plain,
    ( k1_funct_1(sK2,k1_funct_1(sK3,sK0(sK3))) != k1_funct_1(k5_relat_1(sK3,sK2),X0_44)
    | sK0(sK3) = X0_44
    | r2_hidden(X0_44,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2441,c_17,c_18,c_19,c_20,c_21,c_23,c_42,c_1278,c_1289])).

cnf(c_3686,plain,
    ( sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3619,c_3112])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_770,plain,
    ( ~ v1_relat_1(X0_41)
    | ~ v1_funct_1(X0_41)
    | v2_funct_1(X0_41)
    | sK1(X0_41) != sK0(X0_41) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_786,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | v2_funct_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_43,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_45,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3686,c_786,c_45,c_23,c_10,c_20,c_13,c_19,c_14])).


%------------------------------------------------------------------------------

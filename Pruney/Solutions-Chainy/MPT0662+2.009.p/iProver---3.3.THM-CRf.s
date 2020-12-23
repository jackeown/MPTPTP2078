%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:59 EST 2020

% Result     : Theorem 7.94s
% Output     : CNFRefutation 7.94s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 207 expanded)
%              Number of clauses        :   45 (  68 expanded)
%              Number of leaves         :    8 (  38 expanded)
%              Depth                    :   21
%              Number of atoms          :  264 ( 783 expanded)
%              Number of equality atoms :  126 ( 276 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
         => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
        & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK3,sK1) != k1_funct_1(k7_relat_1(sK3,sK2),sK1)
      & r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2)))
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k1_funct_1(sK3,sK1) != k1_funct_1(k7_relat_1(sK3,sK2),sK1)
    & r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2)))
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f23])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
            & r2_hidden(sK0(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

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

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = X3
      | ~ r2_hidden(X3,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X3] :
      ( k1_funct_1(k6_relat_1(X0),X3) = X3
      | ~ r2_hidden(X3,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    k1_funct_1(sK3,sK1) != k1_funct_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_15117,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_15118,plain,
    ( r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_15123,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_15339,plain,
    ( r2_hidden(sK1,sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_15118,c_15123])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_17,plain,
    ( r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6374,plain,
    ( ~ r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2)))
    | r2_hidden(sK1,sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_6375,plain,
    ( r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top
    | r2_hidden(sK1,sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6374])).

cnf(c_15458,plain,
    ( r2_hidden(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15339,c_15,c_17,c_6375])).

cnf(c_10,plain,
    ( ~ v1_funct_1(k6_relat_1(X0))
    | ~ v1_relat_1(k6_relat_1(X0))
    | k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_5,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_4,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_83,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_5,c_4])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_15119,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_15583,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2))
    | r2_hidden(X2,X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_83,c_15119])).

cnf(c_33,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_36,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_17754,plain,
    ( v1_relat_1(X1) != iProver_top
    | k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2))
    | r2_hidden(X2,X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15583,c_33,c_36])).

cnf(c_17755,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2))
    | r2_hidden(X2,X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_17754])).

cnf(c_17768,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),X0),sK1) = k1_funct_1(X0,k1_funct_1(k6_relat_1(sK2),sK1))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15458,c_17755])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_funct_1(k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1))
    | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_6239,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6240,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6241,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6290,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6239,c_6240,c_6241])).

cnf(c_6343,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6290])).

cnf(c_15018,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_6343])).

cnf(c_15112,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15018])).

cnf(c_15463,plain,
    ( k1_funct_1(k6_relat_1(sK2),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_15458,c_15112])).

cnf(c_17772,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),X0),sK1) = k1_funct_1(X0,sK1)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17768,c_15463])).

cnf(c_25872,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) = k1_funct_1(sK3,sK1)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_15117,c_17772])).

cnf(c_15116,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_15122,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_15314,plain,
    ( k5_relat_1(k6_relat_1(X0),sK3) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_15116,c_15122])).

cnf(c_25875,plain,
    ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(sK3,sK1)
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_25872,c_15314])).

cnf(c_26093,plain,
    ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(sK3,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25875,c_15])).

cnf(c_11,negated_conjecture,
    ( k1_funct_1(sK3,sK1) != k1_funct_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_26097,plain,
    ( k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
    inference(demodulation,[status(thm)],[c_26093,c_11])).

cnf(c_26098,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_26097])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.94/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.94/1.48  
% 7.94/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.94/1.48  
% 7.94/1.48  ------  iProver source info
% 7.94/1.48  
% 7.94/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.94/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.94/1.48  git: non_committed_changes: false
% 7.94/1.48  git: last_make_outside_of_git: false
% 7.94/1.48  
% 7.94/1.48  ------ 
% 7.94/1.48  ------ Parsing...
% 7.94/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  ------ Proving...
% 7.94/1.48  ------ Problem Properties 
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  clauses                                 15
% 7.94/1.48  conjectures                             4
% 7.94/1.48  EPR                                     2
% 7.94/1.48  Horn                                    14
% 7.94/1.48  unary                                   7
% 7.94/1.48  binary                                  1
% 7.94/1.48  lits                                    37
% 7.94/1.48  lits eq                                 8
% 7.94/1.48  fd_pure                                 0
% 7.94/1.48  fd_pseudo                               0
% 7.94/1.48  fd_cond                                 0
% 7.94/1.48  fd_pseudo_cond                          0
% 7.94/1.48  AC symbols                              0
% 7.94/1.48  
% 7.94/1.48  ------ Input Options Time Limit: Unbounded
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing...
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 7.94/1.48  Current options:
% 7.94/1.48  ------ 
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing...
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing...
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing...
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 11 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.94/1.48  
% 7.94/1.48  ------ Proving...
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  % SZS status Theorem for theBenchmark.p
% 7.94/1.48  
% 7.94/1.48   Resolution empty clause
% 7.94/1.48  
% 7.94/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.94/1.48  
% 7.94/1.48  fof(f6,conjecture,(
% 7.94/1.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 7.94/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.48  
% 7.94/1.48  fof(f7,negated_conjecture,(
% 7.94/1.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 7.94/1.48    inference(negated_conjecture,[],[f6])).
% 7.94/1.48  
% 7.94/1.48  fof(f14,plain,(
% 7.94/1.48    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 7.94/1.48    inference(ennf_transformation,[],[f7])).
% 7.94/1.48  
% 7.94/1.48  fof(f15,plain,(
% 7.94/1.48    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.94/1.48    inference(flattening,[],[f14])).
% 7.94/1.48  
% 7.94/1.48  fof(f23,plain,(
% 7.94/1.48    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK3,sK1) != k1_funct_1(k7_relat_1(sK3,sK2),sK1) & r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2))) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 7.94/1.48    introduced(choice_axiom,[])).
% 7.94/1.48  
% 7.94/1.48  fof(f24,plain,(
% 7.94/1.48    k1_funct_1(sK3,sK1) != k1_funct_1(k7_relat_1(sK3,sK2),sK1) & r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2))) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 7.94/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f23])).
% 7.94/1.48  
% 7.94/1.48  fof(f37,plain,(
% 7.94/1.48    v1_funct_1(sK3)),
% 7.94/1.48    inference(cnf_transformation,[],[f24])).
% 7.94/1.48  
% 7.94/1.48  fof(f38,plain,(
% 7.94/1.48    r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2)))),
% 7.94/1.48    inference(cnf_transformation,[],[f24])).
% 7.94/1.48  
% 7.94/1.48  fof(f1,axiom,(
% 7.94/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 7.94/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.48  
% 7.94/1.48  fof(f8,plain,(
% 7.94/1.48    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 7.94/1.48    inference(ennf_transformation,[],[f1])).
% 7.94/1.48  
% 7.94/1.48  fof(f16,plain,(
% 7.94/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 7.94/1.48    inference(nnf_transformation,[],[f8])).
% 7.94/1.48  
% 7.94/1.48  fof(f17,plain,(
% 7.94/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 7.94/1.48    inference(flattening,[],[f16])).
% 7.94/1.48  
% 7.94/1.48  fof(f25,plain,(
% 7.94/1.48    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 7.94/1.48    inference(cnf_transformation,[],[f17])).
% 7.94/1.48  
% 7.94/1.48  fof(f36,plain,(
% 7.94/1.48    v1_relat_1(sK3)),
% 7.94/1.48    inference(cnf_transformation,[],[f24])).
% 7.94/1.48  
% 7.94/1.48  fof(f5,axiom,(
% 7.94/1.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 7.94/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.48  
% 7.94/1.48  fof(f12,plain,(
% 7.94/1.48    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.94/1.48    inference(ennf_transformation,[],[f5])).
% 7.94/1.48  
% 7.94/1.48  fof(f13,plain,(
% 7.94/1.48    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.94/1.48    inference(flattening,[],[f12])).
% 7.94/1.48  
% 7.94/1.48  fof(f18,plain,(
% 7.94/1.48    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.94/1.48    inference(nnf_transformation,[],[f13])).
% 7.94/1.48  
% 7.94/1.48  fof(f19,plain,(
% 7.94/1.48    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.94/1.48    inference(flattening,[],[f18])).
% 7.94/1.48  
% 7.94/1.48  fof(f20,plain,(
% 7.94/1.48    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.94/1.48    inference(rectify,[],[f19])).
% 7.94/1.48  
% 7.94/1.48  fof(f21,plain,(
% 7.94/1.48    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.94/1.48    introduced(choice_axiom,[])).
% 7.94/1.48  
% 7.94/1.48  fof(f22,plain,(
% 7.94/1.48    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.94/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 7.94/1.48  
% 7.94/1.48  fof(f32,plain,(
% 7.94/1.48    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | k6_relat_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.94/1.48    inference(cnf_transformation,[],[f22])).
% 7.94/1.48  
% 7.94/1.48  fof(f43,plain,(
% 7.94/1.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0 | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 7.94/1.48    inference(equality_resolution,[],[f32])).
% 7.94/1.48  
% 7.94/1.48  fof(f3,axiom,(
% 7.94/1.48    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.94/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.48  
% 7.94/1.48  fof(f29,plain,(
% 7.94/1.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.94/1.48    inference(cnf_transformation,[],[f3])).
% 7.94/1.48  
% 7.94/1.48  fof(f30,plain,(
% 7.94/1.48    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 7.94/1.48    inference(cnf_transformation,[],[f3])).
% 7.94/1.48  
% 7.94/1.48  fof(f4,axiom,(
% 7.94/1.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0))))),
% 7.94/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.48  
% 7.94/1.48  fof(f10,plain,(
% 7.94/1.48    ! [X0,X1] : (! [X2] : ((k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.94/1.48    inference(ennf_transformation,[],[f4])).
% 7.94/1.48  
% 7.94/1.48  fof(f11,plain,(
% 7.94/1.48    ! [X0,X1] : (! [X2] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.94/1.48    inference(flattening,[],[f10])).
% 7.94/1.48  
% 7.94/1.48  fof(f31,plain,(
% 7.94/1.48    ( ! [X2,X0,X1] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.94/1.48    inference(cnf_transformation,[],[f11])).
% 7.94/1.48  
% 7.94/1.48  fof(f33,plain,(
% 7.94/1.48    ( ! [X0,X3,X1] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0) | k6_relat_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.94/1.48    inference(cnf_transformation,[],[f22])).
% 7.94/1.48  
% 7.94/1.48  fof(f42,plain,(
% 7.94/1.48    ( ! [X0,X3] : (k1_funct_1(k6_relat_1(X0),X3) = X3 | ~r2_hidden(X3,X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 7.94/1.48    inference(equality_resolution,[],[f33])).
% 7.94/1.48  
% 7.94/1.48  fof(f2,axiom,(
% 7.94/1.48    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 7.94/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.48  
% 7.94/1.48  fof(f9,plain,(
% 7.94/1.48    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 7.94/1.48    inference(ennf_transformation,[],[f2])).
% 7.94/1.48  
% 7.94/1.48  fof(f28,plain,(
% 7.94/1.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 7.94/1.48    inference(cnf_transformation,[],[f9])).
% 7.94/1.48  
% 7.94/1.48  fof(f39,plain,(
% 7.94/1.48    k1_funct_1(sK3,sK1) != k1_funct_1(k7_relat_1(sK3,sK2),sK1)),
% 7.94/1.48    inference(cnf_transformation,[],[f24])).
% 7.94/1.48  
% 7.94/1.48  cnf(c_13,negated_conjecture,
% 7.94/1.48      ( v1_funct_1(sK3) ),
% 7.94/1.48      inference(cnf_transformation,[],[f37]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_15117,plain,
% 7.94/1.48      ( v1_funct_1(sK3) = iProver_top ),
% 7.94/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_12,negated_conjecture,
% 7.94/1.48      ( r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2))) ),
% 7.94/1.48      inference(cnf_transformation,[],[f38]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_15118,plain,
% 7.94/1.48      ( r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top ),
% 7.94/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_2,plain,
% 7.94/1.48      ( r2_hidden(X0,X1)
% 7.94/1.48      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 7.94/1.48      | ~ v1_relat_1(X2) ),
% 7.94/1.48      inference(cnf_transformation,[],[f25]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_15123,plain,
% 7.94/1.48      ( r2_hidden(X0,X1) = iProver_top
% 7.94/1.48      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
% 7.94/1.48      | v1_relat_1(X2) != iProver_top ),
% 7.94/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_15339,plain,
% 7.94/1.48      ( r2_hidden(sK1,sK2) = iProver_top | v1_relat_1(sK3) != iProver_top ),
% 7.94/1.48      inference(superposition,[status(thm)],[c_15118,c_15123]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_14,negated_conjecture,
% 7.94/1.48      ( v1_relat_1(sK3) ),
% 7.94/1.48      inference(cnf_transformation,[],[f36]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_15,plain,
% 7.94/1.48      ( v1_relat_1(sK3) = iProver_top ),
% 7.94/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_17,plain,
% 7.94/1.48      ( r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top ),
% 7.94/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_6374,plain,
% 7.94/1.48      ( ~ r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2)))
% 7.94/1.48      | r2_hidden(sK1,sK2)
% 7.94/1.48      | ~ v1_relat_1(sK3) ),
% 7.94/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_6375,plain,
% 7.94/1.48      ( r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top
% 7.94/1.48      | r2_hidden(sK1,sK2) = iProver_top
% 7.94/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.94/1.48      inference(predicate_to_equality,[status(thm)],[c_6374]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_15458,plain,
% 7.94/1.48      ( r2_hidden(sK1,sK2) = iProver_top ),
% 7.94/1.48      inference(global_propositional_subsumption,
% 7.94/1.48                [status(thm)],
% 7.94/1.48                [c_15339,c_15,c_17,c_6375]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_10,plain,
% 7.94/1.48      ( ~ v1_funct_1(k6_relat_1(X0))
% 7.94/1.48      | ~ v1_relat_1(k6_relat_1(X0))
% 7.94/1.48      | k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.94/1.48      inference(cnf_transformation,[],[f43]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_5,plain,
% 7.94/1.48      ( v1_relat_1(k6_relat_1(X0)) ),
% 7.94/1.48      inference(cnf_transformation,[],[f29]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_4,plain,
% 7.94/1.48      ( v1_funct_1(k6_relat_1(X0)) ),
% 7.94/1.48      inference(cnf_transformation,[],[f30]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_83,plain,
% 7.94/1.48      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.94/1.48      inference(global_propositional_subsumption,[status(thm)],[c_10,c_5,c_4]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_6,plain,
% 7.94/1.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.94/1.48      | ~ v1_funct_1(X2)
% 7.94/1.48      | ~ v1_funct_1(X1)
% 7.94/1.48      | ~ v1_relat_1(X2)
% 7.94/1.48      | ~ v1_relat_1(X1)
% 7.94/1.48      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 7.94/1.48      inference(cnf_transformation,[],[f31]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_15119,plain,
% 7.94/1.48      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 7.94/1.48      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 7.94/1.48      | v1_funct_1(X1) != iProver_top
% 7.94/1.48      | v1_funct_1(X0) != iProver_top
% 7.94/1.48      | v1_relat_1(X1) != iProver_top
% 7.94/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.94/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_15583,plain,
% 7.94/1.48      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2))
% 7.94/1.48      | r2_hidden(X2,X0) != iProver_top
% 7.94/1.48      | v1_funct_1(X1) != iProver_top
% 7.94/1.48      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 7.94/1.48      | v1_relat_1(X1) != iProver_top
% 7.94/1.48      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.94/1.48      inference(superposition,[status(thm)],[c_83,c_15119]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_33,plain,
% 7.94/1.48      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.94/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_36,plain,
% 7.94/1.48      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 7.94/1.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_17754,plain,
% 7.94/1.48      ( v1_relat_1(X1) != iProver_top
% 7.94/1.48      | k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2))
% 7.94/1.48      | r2_hidden(X2,X0) != iProver_top
% 7.94/1.48      | v1_funct_1(X1) != iProver_top ),
% 7.94/1.48      inference(global_propositional_subsumption,
% 7.94/1.48                [status(thm)],
% 7.94/1.48                [c_15583,c_33,c_36]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_17755,plain,
% 7.94/1.48      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2))
% 7.94/1.48      | r2_hidden(X2,X0) != iProver_top
% 7.94/1.48      | v1_funct_1(X1) != iProver_top
% 7.94/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.94/1.48      inference(renaming,[status(thm)],[c_17754]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_17768,plain,
% 7.94/1.48      ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),X0),sK1) = k1_funct_1(X0,k1_funct_1(k6_relat_1(sK2),sK1))
% 7.94/1.48      | v1_funct_1(X0) != iProver_top
% 7.94/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.94/1.48      inference(superposition,[status(thm)],[c_15458,c_17755]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_9,plain,
% 7.94/1.48      ( ~ r2_hidden(X0,X1)
% 7.94/1.48      | ~ v1_funct_1(k6_relat_1(X1))
% 7.94/1.48      | ~ v1_relat_1(k6_relat_1(X1))
% 7.94/1.48      | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
% 7.94/1.48      inference(cnf_transformation,[],[f42]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_6239,plain,
% 7.94/1.48      ( k1_funct_1(k6_relat_1(X0),X1) = X1
% 7.94/1.48      | r2_hidden(X1,X0) != iProver_top
% 7.94/1.48      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 7.94/1.48      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.94/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_6240,plain,
% 7.94/1.48      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.94/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_6241,plain,
% 7.94/1.48      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 7.94/1.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_6290,plain,
% 7.94/1.48      ( k1_funct_1(k6_relat_1(X0),X1) = X1 | r2_hidden(X1,X0) != iProver_top ),
% 7.94/1.48      inference(forward_subsumption_resolution,
% 7.94/1.48                [status(thm)],
% 7.94/1.48                [c_6239,c_6240,c_6241]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_6343,plain,
% 7.94/1.48      ( ~ r2_hidden(X0,X1) | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
% 7.94/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_6290]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_15018,plain,
% 7.94/1.48      ( ~ r2_hidden(X0,X1) | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
% 7.94/1.48      inference(global_propositional_subsumption,[status(thm)],[c_9,c_6343]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_15112,plain,
% 7.94/1.48      ( k1_funct_1(k6_relat_1(X0),X1) = X1 | r2_hidden(X1,X0) != iProver_top ),
% 7.94/1.48      inference(predicate_to_equality,[status(thm)],[c_15018]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_15463,plain,
% 7.94/1.48      ( k1_funct_1(k6_relat_1(sK2),sK1) = sK1 ),
% 7.94/1.48      inference(superposition,[status(thm)],[c_15458,c_15112]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_17772,plain,
% 7.94/1.48      ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),X0),sK1) = k1_funct_1(X0,sK1)
% 7.94/1.48      | v1_funct_1(X0) != iProver_top
% 7.94/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.94/1.48      inference(light_normalisation,[status(thm)],[c_17768,c_15463]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_25872,plain,
% 7.94/1.48      ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) = k1_funct_1(sK3,sK1)
% 7.94/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.94/1.48      inference(superposition,[status(thm)],[c_15117,c_17772]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_15116,plain,
% 7.94/1.48      ( v1_relat_1(sK3) = iProver_top ),
% 7.94/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_3,plain,
% 7.94/1.48      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 7.94/1.48      inference(cnf_transformation,[],[f28]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_15122,plain,
% 7.94/1.48      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 7.94/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.94/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_15314,plain,
% 7.94/1.48      ( k5_relat_1(k6_relat_1(X0),sK3) = k7_relat_1(sK3,X0) ),
% 7.94/1.48      inference(superposition,[status(thm)],[c_15116,c_15122]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_25875,plain,
% 7.94/1.48      ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(sK3,sK1)
% 7.94/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.94/1.48      inference(demodulation,[status(thm)],[c_25872,c_15314]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_26093,plain,
% 7.94/1.48      ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(sK3,sK1) ),
% 7.94/1.48      inference(global_propositional_subsumption,[status(thm)],[c_25875,c_15]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_11,negated_conjecture,
% 7.94/1.48      ( k1_funct_1(sK3,sK1) != k1_funct_1(k7_relat_1(sK3,sK2),sK1) ),
% 7.94/1.48      inference(cnf_transformation,[],[f39]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_26097,plain,
% 7.94/1.48      ( k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
% 7.94/1.48      inference(demodulation,[status(thm)],[c_26093,c_11]) ).
% 7.94/1.48  
% 7.94/1.48  cnf(c_26098,plain,
% 7.94/1.48      ( $false ),
% 7.94/1.48      inference(equality_resolution_simp,[status(thm)],[c_26097]) ).
% 7.94/1.48  
% 7.94/1.48  
% 7.94/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.94/1.48  
% 7.94/1.48  ------                               Statistics
% 7.94/1.48  
% 7.94/1.48  ------ Selected
% 7.94/1.48  
% 7.94/1.48  total_time:                             0.893
% 7.94/1.48  
%------------------------------------------------------------------------------

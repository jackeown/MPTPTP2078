%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:06 EST 2020

% Result     : Theorem 4.00s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 166 expanded)
%              Number of clauses        :   43 (  52 expanded)
%              Number of leaves         :   10 (  33 expanded)
%              Depth                    :   16
%              Number of atoms          :  279 ( 699 expanded)
%              Number of equality atoms :   73 (  79 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X0,X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
       => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r2_hidden(X0,X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
         => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
        & r2_hidden(X0,X1)
        & r2_hidden(X0,k1_relat_1(X2))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(k7_relat_1(sK3,sK2)))
      & r2_hidden(sK1,sK2)
      & r2_hidden(sK1,k1_relat_1(sK3))
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(k7_relat_1(sK3,sK2)))
    & r2_hidden(sK1,sK2)
    & r2_hidden(sK1,k1_relat_1(sK3))
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f24])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    r2_hidden(sK1,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(k7_relat_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(flattening,[],[f19])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_9170,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_9168,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k7_relat_1(X0,X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9162,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_9164,plain,
    ( r2_hidden(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_9166,plain,
    ( k1_funct_1(k7_relat_1(X0,X1),X2) = k1_funct_1(X0,X2)
    | r2_hidden(X2,X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10367,plain,
    ( k1_funct_1(k7_relat_1(X0,sK2),sK1) = k1_funct_1(X0,sK1)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9164,c_9166])).

cnf(c_10717,plain,
    ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(sK3,sK1)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9162,c_10367])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2827,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(k7_relat_1(X0,sK2),sK1) = k1_funct_1(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2829,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_2827])).

cnf(c_10735,plain,
    ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(sK3,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10717,c_16,c_15,c_13,c_2829])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_9167,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12244,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(k7_relat_1(sK3,sK2))) = iProver_top
    | r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10735,c_9167])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK1,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_19,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_20,plain,
    ( r2_hidden(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(k7_relat_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_21,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(k7_relat_1(sK3,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_6024,plain,
    ( ~ r2_hidden(sK1,X0)
    | r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),X0))
    | ~ r2_hidden(sK1,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6089,plain,
    ( r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))
    | ~ r2_hidden(sK1,k1_relat_1(sK3))
    | ~ r2_hidden(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_6024])).

cnf(c_6090,plain,
    ( r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) = iProver_top
    | r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6089])).

cnf(c_235,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_9500,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))
    | X1 != k3_xboole_0(k1_relat_1(sK3),sK2)
    | X0 != sK1 ),
    inference(instantiation,[status(thm)],[c_235])).

cnf(c_12725,plain,
    ( r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))
    | X0 != k3_xboole_0(k1_relat_1(sK3),sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_9500])).

cnf(c_12726,plain,
    ( r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))
    | X0 != k3_xboole_0(k1_relat_1(sK3),sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_12725])).

cnf(c_13465,plain,
    ( ~ r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))
    | r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2)))
    | k1_relat_1(k7_relat_1(sK3,sK2)) != k3_xboole_0(k1_relat_1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_12726])).

cnf(c_13466,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != k3_xboole_0(k1_relat_1(sK3),sK2)
    | r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) != iProver_top
    | r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13465])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_13546,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,sK2)) = k3_xboole_0(k1_relat_1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_13622,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12244,c_16,c_19,c_20,c_21,c_6090,c_13466,c_13546])).

cnf(c_13628,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9168,c_13622])).

cnf(c_17,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14032,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13628,c_17,c_18])).

cnf(c_14037,plain,
    ( v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9170,c_14032])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14037,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.01/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.31  % Computer   : n003.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 09:40:27 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 4.00/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/0.96  
% 4.00/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.00/0.96  
% 4.00/0.96  ------  iProver source info
% 4.00/0.96  
% 4.00/0.96  git: date: 2020-06-30 10:37:57 +0100
% 4.00/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.00/0.96  git: non_committed_changes: false
% 4.00/0.96  git: last_make_outside_of_git: false
% 4.00/0.96  
% 4.00/0.96  ------ 
% 4.00/0.96  ------ Parsing...
% 4.00/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.00/0.96  ------ Proving...
% 4.00/0.96  ------ Problem Properties 
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  clauses                                 16
% 4.00/0.96  conjectures                             5
% 4.00/0.96  EPR                                     3
% 4.00/0.96  Horn                                    14
% 4.00/0.96  unary                                   5
% 4.00/0.96  binary                                  4
% 4.00/0.96  lits                                    37
% 4.00/0.96  lits eq                                 5
% 4.00/0.96  fd_pure                                 0
% 4.00/0.96  fd_pseudo                               0
% 4.00/0.96  fd_cond                                 0
% 4.00/0.96  fd_pseudo_cond                          3
% 4.00/0.96  AC symbols                              0
% 4.00/0.96  
% 4.00/0.96  ------ Input Options Time Limit: Unbounded
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing...
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 4.00/0.96  Current options:
% 4.00/0.96  ------ 
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  ------ Proving...
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.00/0.96  
% 4.00/0.96  ------ Proving...
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.00/0.96  
% 4.00/0.96  ------ Proving...
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.00/0.96  
% 4.00/0.96  ------ Proving...
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.00/0.96  
% 4.00/0.96  ------ Proving...
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.00/0.96  
% 4.00/0.96  ------ Proving...
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.00/0.96  
% 4.00/0.96  ------ Proving...
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.00/0.96  
% 4.00/0.96  ------ Proving...
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.00/0.96  
% 4.00/0.96  ------ Proving...
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.00/0.96  
% 4.00/0.96  ------ Proving...
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.00/0.96  
% 4.00/0.96  ------ Proving...
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.00/0.96  
% 4.00/0.96  ------ Proving...
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.00/0.96  
% 4.00/0.96  ------ Proving...
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  % SZS status Theorem for theBenchmark.p
% 4.00/0.96  
% 4.00/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 4.00/0.96  
% 4.00/0.96  fof(f2,axiom,(
% 4.00/0.96    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 4.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.96  
% 4.00/0.96  fof(f9,plain,(
% 4.00/0.96    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 4.00/0.96    inference(ennf_transformation,[],[f2])).
% 4.00/0.96  
% 4.00/0.96  fof(f32,plain,(
% 4.00/0.96    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 4.00/0.96    inference(cnf_transformation,[],[f9])).
% 4.00/0.96  
% 4.00/0.96  fof(f4,axiom,(
% 4.00/0.96    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 4.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.96  
% 4.00/0.96  fof(f11,plain,(
% 4.00/0.96    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.00/0.96    inference(ennf_transformation,[],[f4])).
% 4.00/0.96  
% 4.00/0.96  fof(f12,plain,(
% 4.00/0.96    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.00/0.96    inference(flattening,[],[f11])).
% 4.00/0.96  
% 4.00/0.96  fof(f35,plain,(
% 4.00/0.96    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.00/0.96    inference(cnf_transformation,[],[f12])).
% 4.00/0.96  
% 4.00/0.96  fof(f7,conjecture,(
% 4.00/0.96    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2))) => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))))),
% 4.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.96  
% 4.00/0.96  fof(f8,negated_conjecture,(
% 4.00/0.96    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2))) => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))))),
% 4.00/0.96    inference(negated_conjecture,[],[f7])).
% 4.00/0.96  
% 4.00/0.96  fof(f17,plain,(
% 4.00/0.96    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) & (r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 4.00/0.96    inference(ennf_transformation,[],[f8])).
% 4.00/0.96  
% 4.00/0.96  fof(f18,plain,(
% 4.00/0.96    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) & r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 4.00/0.96    inference(flattening,[],[f17])).
% 4.00/0.96  
% 4.00/0.96  fof(f24,plain,(
% 4.00/0.96    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) & r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(k7_relat_1(sK3,sK2))) & r2_hidden(sK1,sK2) & r2_hidden(sK1,k1_relat_1(sK3)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 4.00/0.96    introduced(choice_axiom,[])).
% 4.00/0.96  
% 4.00/0.96  fof(f25,plain,(
% 4.00/0.96    ~r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(k7_relat_1(sK3,sK2))) & r2_hidden(sK1,sK2) & r2_hidden(sK1,k1_relat_1(sK3)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 4.00/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f24])).
% 4.00/0.96  
% 4.00/0.96  fof(f39,plain,(
% 4.00/0.96    v1_funct_1(sK3)),
% 4.00/0.96    inference(cnf_transformation,[],[f25])).
% 4.00/0.96  
% 4.00/0.96  fof(f41,plain,(
% 4.00/0.96    r2_hidden(sK1,sK2)),
% 4.00/0.96    inference(cnf_transformation,[],[f25])).
% 4.00/0.96  
% 4.00/0.96  fof(f6,axiom,(
% 4.00/0.96    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 4.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.96  
% 4.00/0.96  fof(f15,plain,(
% 4.00/0.96    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.00/0.96    inference(ennf_transformation,[],[f6])).
% 4.00/0.96  
% 4.00/0.96  fof(f16,plain,(
% 4.00/0.96    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.00/0.96    inference(flattening,[],[f15])).
% 4.00/0.96  
% 4.00/0.96  fof(f37,plain,(
% 4.00/0.96    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.00/0.96    inference(cnf_transformation,[],[f16])).
% 4.00/0.96  
% 4.00/0.96  fof(f38,plain,(
% 4.00/0.96    v1_relat_1(sK3)),
% 4.00/0.96    inference(cnf_transformation,[],[f25])).
% 4.00/0.96  
% 4.00/0.96  fof(f5,axiom,(
% 4.00/0.96    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 4.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.96  
% 4.00/0.96  fof(f13,plain,(
% 4.00/0.96    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.00/0.96    inference(ennf_transformation,[],[f5])).
% 4.00/0.96  
% 4.00/0.96  fof(f14,plain,(
% 4.00/0.96    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.00/0.96    inference(flattening,[],[f13])).
% 4.00/0.96  
% 4.00/0.96  fof(f36,plain,(
% 4.00/0.96    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.00/0.96    inference(cnf_transformation,[],[f14])).
% 4.00/0.96  
% 4.00/0.96  fof(f40,plain,(
% 4.00/0.96    r2_hidden(sK1,k1_relat_1(sK3))),
% 4.00/0.96    inference(cnf_transformation,[],[f25])).
% 4.00/0.96  
% 4.00/0.96  fof(f42,plain,(
% 4.00/0.96    ~r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(k7_relat_1(sK3,sK2)))),
% 4.00/0.96    inference(cnf_transformation,[],[f25])).
% 4.00/0.96  
% 4.00/0.96  fof(f1,axiom,(
% 4.00/0.96    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.96  
% 4.00/0.96  fof(f19,plain,(
% 4.00/0.96    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.00/0.96    inference(nnf_transformation,[],[f1])).
% 4.00/0.96  
% 4.00/0.96  fof(f20,plain,(
% 4.00/0.96    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.00/0.96    inference(flattening,[],[f19])).
% 4.00/0.96  
% 4.00/0.96  fof(f21,plain,(
% 4.00/0.96    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.00/0.96    inference(rectify,[],[f20])).
% 4.00/0.96  
% 4.00/0.96  fof(f22,plain,(
% 4.00/0.96    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 4.00/0.96    introduced(choice_axiom,[])).
% 4.00/0.96  
% 4.00/0.96  fof(f23,plain,(
% 4.00/0.96    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.00/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 4.00/0.96  
% 4.00/0.96  fof(f28,plain,(
% 4.00/0.96    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 4.00/0.96    inference(cnf_transformation,[],[f23])).
% 4.00/0.96  
% 4.00/0.96  fof(f43,plain,(
% 4.00/0.96    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 4.00/0.96    inference(equality_resolution,[],[f28])).
% 4.00/0.96  
% 4.00/0.96  fof(f3,axiom,(
% 4.00/0.96    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 4.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.96  
% 4.00/0.96  fof(f10,plain,(
% 4.00/0.96    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 4.00/0.96    inference(ennf_transformation,[],[f3])).
% 4.00/0.96  
% 4.00/0.96  fof(f33,plain,(
% 4.00/0.96    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 4.00/0.96    inference(cnf_transformation,[],[f10])).
% 4.00/0.96  
% 4.00/0.96  cnf(c_6,plain,
% 4.00/0.96      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 4.00/0.96      inference(cnf_transformation,[],[f32]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_9170,plain,
% 4.00/0.96      ( v1_relat_1(X0) != iProver_top
% 4.00/0.96      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_8,plain,
% 4.00/0.96      ( ~ v1_funct_1(X0)
% 4.00/0.96      | v1_funct_1(k7_relat_1(X0,X1))
% 4.00/0.96      | ~ v1_relat_1(X0) ),
% 4.00/0.96      inference(cnf_transformation,[],[f35]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_9168,plain,
% 4.00/0.96      ( v1_funct_1(X0) != iProver_top
% 4.00/0.96      | v1_funct_1(k7_relat_1(X0,X1)) = iProver_top
% 4.00/0.96      | v1_relat_1(X0) != iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_15,negated_conjecture,
% 4.00/0.96      ( v1_funct_1(sK3) ),
% 4.00/0.96      inference(cnf_transformation,[],[f39]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_9162,plain,
% 4.00/0.96      ( v1_funct_1(sK3) = iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_13,negated_conjecture,
% 4.00/0.96      ( r2_hidden(sK1,sK2) ),
% 4.00/0.96      inference(cnf_transformation,[],[f41]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_9164,plain,
% 4.00/0.96      ( r2_hidden(sK1,sK2) = iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_11,plain,
% 4.00/0.96      ( ~ r2_hidden(X0,X1)
% 4.00/0.96      | ~ v1_funct_1(X2)
% 4.00/0.96      | ~ v1_relat_1(X2)
% 4.00/0.96      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
% 4.00/0.96      inference(cnf_transformation,[],[f37]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_9166,plain,
% 4.00/0.96      ( k1_funct_1(k7_relat_1(X0,X1),X2) = k1_funct_1(X0,X2)
% 4.00/0.96      | r2_hidden(X2,X1) != iProver_top
% 4.00/0.96      | v1_funct_1(X0) != iProver_top
% 4.00/0.96      | v1_relat_1(X0) != iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_10367,plain,
% 4.00/0.96      ( k1_funct_1(k7_relat_1(X0,sK2),sK1) = k1_funct_1(X0,sK1)
% 4.00/0.96      | v1_funct_1(X0) != iProver_top
% 4.00/0.96      | v1_relat_1(X0) != iProver_top ),
% 4.00/0.96      inference(superposition,[status(thm)],[c_9164,c_9166]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_10717,plain,
% 4.00/0.96      ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(sK3,sK1)
% 4.00/0.96      | v1_relat_1(sK3) != iProver_top ),
% 4.00/0.96      inference(superposition,[status(thm)],[c_9162,c_10367]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_16,negated_conjecture,
% 4.00/0.96      ( v1_relat_1(sK3) ),
% 4.00/0.96      inference(cnf_transformation,[],[f38]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2827,plain,
% 4.00/0.96      ( ~ r2_hidden(sK1,sK2)
% 4.00/0.96      | ~ v1_funct_1(X0)
% 4.00/0.96      | ~ v1_relat_1(X0)
% 4.00/0.96      | k1_funct_1(k7_relat_1(X0,sK2),sK1) = k1_funct_1(X0,sK1) ),
% 4.00/0.96      inference(instantiation,[status(thm)],[c_11]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2829,plain,
% 4.00/0.96      ( ~ r2_hidden(sK1,sK2)
% 4.00/0.96      | ~ v1_funct_1(sK3)
% 4.00/0.96      | ~ v1_relat_1(sK3)
% 4.00/0.96      | k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(sK3,sK1) ),
% 4.00/0.96      inference(instantiation,[status(thm)],[c_2827]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_10735,plain,
% 4.00/0.96      ( k1_funct_1(k7_relat_1(sK3,sK2),sK1) = k1_funct_1(sK3,sK1) ),
% 4.00/0.96      inference(global_propositional_subsumption,
% 4.00/0.96                [status(thm)],
% 4.00/0.96                [c_10717,c_16,c_15,c_13,c_2829]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_10,plain,
% 4.00/0.96      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.00/0.96      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 4.00/0.96      | ~ v1_funct_1(X1)
% 4.00/0.96      | ~ v1_relat_1(X1) ),
% 4.00/0.96      inference(cnf_transformation,[],[f36]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_9167,plain,
% 4.00/0.96      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 4.00/0.96      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 4.00/0.96      | v1_funct_1(X1) != iProver_top
% 4.00/0.96      | v1_relat_1(X1) != iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_12244,plain,
% 4.00/0.96      ( r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(k7_relat_1(sK3,sK2))) = iProver_top
% 4.00/0.96      | r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top
% 4.00/0.96      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 4.00/0.96      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 4.00/0.96      inference(superposition,[status(thm)],[c_10735,c_9167]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_14,negated_conjecture,
% 4.00/0.96      ( r2_hidden(sK1,k1_relat_1(sK3)) ),
% 4.00/0.96      inference(cnf_transformation,[],[f40]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_19,plain,
% 4.00/0.96      ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_20,plain,
% 4.00/0.96      ( r2_hidden(sK1,sK2) = iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_12,negated_conjecture,
% 4.00/0.96      ( ~ r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(k7_relat_1(sK3,sK2))) ),
% 4.00/0.96      inference(cnf_transformation,[],[f42]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_21,plain,
% 4.00/0.96      ( r2_hidden(k1_funct_1(sK3,sK1),k2_relat_1(k7_relat_1(sK3,sK2))) != iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_3,plain,
% 4.00/0.96      ( ~ r2_hidden(X0,X1)
% 4.00/0.96      | ~ r2_hidden(X0,X2)
% 4.00/0.96      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 4.00/0.96      inference(cnf_transformation,[],[f43]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_6024,plain,
% 4.00/0.96      ( ~ r2_hidden(sK1,X0)
% 4.00/0.96      | r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),X0))
% 4.00/0.96      | ~ r2_hidden(sK1,k1_relat_1(sK3)) ),
% 4.00/0.96      inference(instantiation,[status(thm)],[c_3]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_6089,plain,
% 4.00/0.96      ( r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))
% 4.00/0.96      | ~ r2_hidden(sK1,k1_relat_1(sK3))
% 4.00/0.96      | ~ r2_hidden(sK1,sK2) ),
% 4.00/0.96      inference(instantiation,[status(thm)],[c_6024]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_6090,plain,
% 4.00/0.96      ( r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) = iProver_top
% 4.00/0.96      | r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top
% 4.00/0.96      | r2_hidden(sK1,sK2) != iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_6089]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_235,plain,
% 4.00/0.96      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.00/0.96      theory(equality) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_9500,plain,
% 4.00/0.96      ( r2_hidden(X0,X1)
% 4.00/0.96      | ~ r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))
% 4.00/0.96      | X1 != k3_xboole_0(k1_relat_1(sK3),sK2)
% 4.00/0.96      | X0 != sK1 ),
% 4.00/0.96      inference(instantiation,[status(thm)],[c_235]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_12725,plain,
% 4.00/0.96      ( r2_hidden(sK1,X0)
% 4.00/0.96      | ~ r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))
% 4.00/0.96      | X0 != k3_xboole_0(k1_relat_1(sK3),sK2)
% 4.00/0.96      | sK1 != sK1 ),
% 4.00/0.96      inference(instantiation,[status(thm)],[c_9500]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_12726,plain,
% 4.00/0.96      ( r2_hidden(sK1,X0)
% 4.00/0.96      | ~ r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))
% 4.00/0.96      | X0 != k3_xboole_0(k1_relat_1(sK3),sK2) ),
% 4.00/0.96      inference(equality_resolution_simp,[status(thm)],[c_12725]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_13465,plain,
% 4.00/0.96      ( ~ r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))
% 4.00/0.96      | r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2)))
% 4.00/0.96      | k1_relat_1(k7_relat_1(sK3,sK2)) != k3_xboole_0(k1_relat_1(sK3),sK2) ),
% 4.00/0.96      inference(instantiation,[status(thm)],[c_12726]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_13466,plain,
% 4.00/0.96      ( k1_relat_1(k7_relat_1(sK3,sK2)) != k3_xboole_0(k1_relat_1(sK3),sK2)
% 4.00/0.96      | r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) != iProver_top
% 4.00/0.96      | r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_13465]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_7,plain,
% 4.00/0.96      ( ~ v1_relat_1(X0)
% 4.00/0.96      | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
% 4.00/0.96      inference(cnf_transformation,[],[f33]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_13546,plain,
% 4.00/0.96      ( ~ v1_relat_1(sK3)
% 4.00/0.96      | k1_relat_1(k7_relat_1(sK3,sK2)) = k3_xboole_0(k1_relat_1(sK3),sK2) ),
% 4.00/0.96      inference(instantiation,[status(thm)],[c_7]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_13622,plain,
% 4.00/0.96      ( v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 4.00/0.96      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 4.00/0.96      inference(global_propositional_subsumption,
% 4.00/0.96                [status(thm)],
% 4.00/0.96                [c_12244,c_16,c_19,c_20,c_21,c_6090,c_13466,c_13546]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_13628,plain,
% 4.00/0.96      ( v1_funct_1(sK3) != iProver_top
% 4.00/0.96      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top
% 4.00/0.96      | v1_relat_1(sK3) != iProver_top ),
% 4.00/0.96      inference(superposition,[status(thm)],[c_9168,c_13622]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_17,plain,
% 4.00/0.96      ( v1_relat_1(sK3) = iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_18,plain,
% 4.00/0.96      ( v1_funct_1(sK3) = iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_14032,plain,
% 4.00/0.96      ( v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 4.00/0.96      inference(global_propositional_subsumption,
% 4.00/0.96                [status(thm)],
% 4.00/0.96                [c_13628,c_17,c_18]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_14037,plain,
% 4.00/0.96      ( v1_relat_1(sK3) != iProver_top ),
% 4.00/0.96      inference(superposition,[status(thm)],[c_9170,c_14032]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(contradiction,plain,
% 4.00/0.96      ( $false ),
% 4.00/0.96      inference(minisat,[status(thm)],[c_14037,c_17]) ).
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 4.00/0.96  
% 4.00/0.96  ------                               Statistics
% 4.00/0.96  
% 4.00/0.96  ------ Selected
% 4.00/0.96  
% 4.00/0.96  total_time:                             0.36
% 4.00/0.96  
%------------------------------------------------------------------------------

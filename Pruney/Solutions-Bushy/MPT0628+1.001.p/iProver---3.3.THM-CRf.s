%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0628+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:46 EST 2020

% Result     : Theorem 1.36s
% Output     : CNFRefutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 360 expanded)
%              Number of clauses        :   51 ( 100 expanded)
%              Number of leaves         :    8 (  86 expanded)
%              Depth                    :   22
%              Number of atoms          :  393 (2010 expanded)
%              Number of equality atoms :  154 ( 513 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,X1) = k1_xboole_0
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k1_relat_1(X1))
             => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) != k1_funct_1(k5_relat_1(X1,X2),X0)
          & r2_hidden(X0,k1_relat_1(X1))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) != k1_funct_1(k5_relat_1(X1,X2),X0)
          & r2_hidden(X0,k1_relat_1(X1))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) != k1_funct_1(k5_relat_1(X1,X2),X0)
          & r2_hidden(X0,k1_relat_1(X1))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_funct_1(k5_relat_1(X1,sK2),X0) != k1_funct_1(sK2,k1_funct_1(X1,X0))
        & r2_hidden(X0,k1_relat_1(X1))
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k1_funct_1(X2,k1_funct_1(X1,X0)) != k1_funct_1(k5_relat_1(X1,X2),X0)
            & r2_hidden(X0,k1_relat_1(X1))
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k1_funct_1(X2,k1_funct_1(sK1,sK0)) != k1_funct_1(k5_relat_1(sK1,X2),sK0)
          & r2_hidden(sK0,k1_relat_1(sK1))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    & r2_hidden(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f21,f20])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    k1_funct_1(k5_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f37,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_521,plain,
    ( k1_funct_1(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_516,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2))) = iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1276,plain,
    ( k1_funct_1(X0,k1_funct_1(X1,X2)) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X0))) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_521,c_516])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_510,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_508,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_513,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_955,plain,
    ( k1_funct_1(X0,k1_funct_1(X1,X2)) = k1_funct_1(k5_relat_1(X1,X0),X2)
    | k1_funct_1(k5_relat_1(X1,X0),X2) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_521,c_513])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_33,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v1_funct_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_36,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2417,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | k1_funct_1(X0,k1_funct_1(X1,X2)) = k1_funct_1(k5_relat_1(X1,X0),X2)
    | k1_funct_1(k5_relat_1(X1,X0),X2) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_955,c_33,c_36])).

cnf(c_2418,plain,
    ( k1_funct_1(X0,k1_funct_1(X1,X2)) = k1_funct_1(k5_relat_1(X1,X0),X2)
    | k1_funct_1(k5_relat_1(X1,X0),X2) = k1_xboole_0
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2417])).

cnf(c_2430,plain,
    ( k1_funct_1(k5_relat_1(sK1,X0),X1) = k1_funct_1(X0,k1_funct_1(sK1,X1))
    | k1_funct_1(k5_relat_1(sK1,X0),X1) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_508,c_2418])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_17,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2839,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k1_funct_1(k5_relat_1(sK1,X0),X1) = k1_xboole_0
    | k1_funct_1(k5_relat_1(sK1,X0),X1) = k1_funct_1(X0,k1_funct_1(sK1,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2430,c_17])).

cnf(c_2840,plain,
    ( k1_funct_1(k5_relat_1(sK1,X0),X1) = k1_funct_1(X0,k1_funct_1(sK1,X1))
    | k1_funct_1(k5_relat_1(sK1,X0),X1) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2839])).

cnf(c_2847,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_xboole_0
    | k1_funct_1(sK2,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_510,c_2840])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2876,plain,
    ( ~ v1_funct_1(sK2)
    | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_xboole_0
    | k1_funct_1(sK2,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2847])).

cnf(c_2964,plain,
    ( k1_funct_1(sK2,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0)
    | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2847,c_12,c_2876])).

cnf(c_2965,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_xboole_0
    | k1_funct_1(sK2,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0) ),
    inference(renaming,[status(thm)],[c_2964])).

cnf(c_10,negated_conjecture,
    ( k1_funct_1(k5_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2971,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK2),sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2965,c_10])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_519,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3058,plain,
    ( r2_hidden(k4_tarski(sK0,k1_xboole_0),k5_relat_1(sK1,sK2)) = iProver_top
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k5_relat_1(sK1,sK2)) != iProver_top
    | v1_funct_1(k5_relat_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2971,c_519])).

cnf(c_16,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_18,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_19,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_994,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,X0)))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK1)
    | k1_funct_1(k5_relat_1(sK1,X0),sK0) = k1_funct_1(X0,k1_funct_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2546,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK1)
    | k1_funct_1(k5_relat_1(sK1,sK2),sK0) = k1_funct_1(sK2,k1_funct_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_2547,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK2),sK0) = k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2546])).

cnf(c_3176,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3058,c_16,c_17,c_18,c_19,c_10,c_2547])).

cnf(c_3959,plain,
    ( k1_funct_1(sK2,k1_funct_1(sK1,sK0)) = k1_xboole_0
    | r2_hidden(sK0,k1_relat_1(sK1)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1276,c_3176])).

cnf(c_2697,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | v1_funct_1(k5_relat_1(sK1,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1257,plain,
    ( v1_relat_1(k5_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_256,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_664,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK2),sK0) != X0
    | k1_funct_1(k5_relat_1(sK1,sK2),sK0) = k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | k1_funct_1(sK2,k1_funct_1(sK1,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_868,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK2),sK0) = k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | k1_funct_1(k5_relat_1(sK1,sK2),sK0) != k1_xboole_0
    | k1_funct_1(sK2,k1_funct_1(sK1,sK0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_664])).

cnf(c_704,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(k5_relat_1(X1,X2))
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_867,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k5_relat_1(sK1,sK2))
    | ~ v1_funct_1(k5_relat_1(sK1,sK2))
    | k1_funct_1(k5_relat_1(sK1,sK2),sK0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_11,negated_conjecture,
    ( r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_20,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3959,c_2697,c_2546,c_1257,c_868,c_867,c_10,c_20,c_19,c_12,c_18,c_13,c_17,c_14,c_16,c_15])).


%------------------------------------------------------------------------------

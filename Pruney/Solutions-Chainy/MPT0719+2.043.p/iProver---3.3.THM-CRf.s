%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:08 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 381 expanded)
%              Number of clauses        :   72 ( 172 expanded)
%              Number of leaves         :   19 (  76 expanded)
%              Depth                    :   25
%              Number of atoms          :  350 (1013 expanded)
%              Number of equality atoms :  169 ( 443 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK0(X0,X1)),k1_funct_1(X0,sK0(X0,X1)))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK0(X0,X1)),k1_funct_1(X0,sK0(X0,X1)))
                & r2_hidden(sK0(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v5_funct_1(X1,X0)
      | r2_hidden(sK0(X0,X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK1(X0,X1)) != sK1(X0,X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK1(X0,X1)) != sK1(X0,X1)
            & r2_hidden(sK1(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f59,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f29,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f41,plain,
    ( ? [X0] :
        ( ~ v5_funct_1(k1_xboole_0,X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v5_funct_1(k1_xboole_0,sK2)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f41])).

fof(f64,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k11_relat_1(X1,X0) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k11_relat_1(X1,X0) != k1_xboole_0 )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k11_relat_1(X1,X0) = k1_xboole_0 )
        & ( k11_relat_1(X1,X0) != k1_xboole_0
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_xboole_0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ~ v5_funct_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_13,plain,
    ( v5_funct_1(X0,X1)
    | r2_hidden(sK0(X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1052,plain,
    ( v5_funct_1(X0,X1) = iProver_top
    | r2_hidden(sK0(X1,X0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_16,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1064,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1063,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1516,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1064,c_1063])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1054,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1647,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_1064,c_1054])).

cnf(c_20,plain,
    ( ~ v1_funct_1(k6_relat_1(X0))
    | ~ v1_relat_1(k6_relat_1(X0))
    | k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_15,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_138,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_16,c_15])).

cnf(c_1652,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_1647,c_138])).

cnf(c_2457,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1516,c_1652])).

cnf(c_2634,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2457,c_1064])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1065,plain,
    ( k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2656,plain,
    ( k9_relat_1(k1_xboole_0,k1_tarski(X0)) = k11_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2634,c_1065])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1061,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2657,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2634,c_1061])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1055,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2664,plain,
    ( k5_relat_1(k6_relat_1(X0),k1_xboole_0) = k7_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2634,c_1055])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1057,plain,
    ( k5_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1467,plain,
    ( k5_relat_1(k6_relat_1(X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1064,c_1057])).

cnf(c_2666,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2664,c_1467])).

cnf(c_2671,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2657,c_2666])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1044,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1517,plain,
    ( k7_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1044,c_1063])).

cnf(c_2077,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1044,c_1061])).

cnf(c_2280,plain,
    ( k9_relat_1(sK2,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1517,c_2077])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1060,plain,
    ( k9_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1507,plain,
    ( k9_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1044,c_1060])).

cnf(c_2283,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2280,c_1507])).

cnf(c_2673,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2671,c_2283])).

cnf(c_2675,plain,
    ( k11_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2656,c_2673])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1058,plain,
    ( k11_relat_1(X0,X1) != k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2945,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2675,c_1058])).

cnf(c_39,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_41,plain,
    ( v1_relat_1(k6_relat_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_638,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_665,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_641,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1289,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k6_relat_1(X1))
    | X0 != k6_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_641])).

cnf(c_1290,plain,
    ( X0 != k6_relat_1(X1)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1289])).

cnf(c_1292,plain,
    ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | v1_relat_1(k6_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1290])).

cnf(c_639,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1634,plain,
    ( X0 != X1
    | X0 = k6_relat_1(X2)
    | k6_relat_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_1635,plain,
    ( k6_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1634])).

cnf(c_2950,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2945,c_41,c_665,c_1292,c_1635,c_2457])).

cnf(c_2957,plain,
    ( v5_funct_1(k1_xboole_0,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1052,c_2950])).

cnf(c_42,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_44,plain,
    ( v1_funct_1(k6_relat_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_650,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1299,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k6_relat_1(X1))
    | X0 != k6_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_650])).

cnf(c_1300,plain,
    ( X0 != k6_relat_1(X1)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(k6_relat_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1299])).

cnf(c_1302,plain,
    ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | v1_funct_1(k6_relat_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1300])).

cnf(c_3025,plain,
    ( v1_relat_1(X0) != iProver_top
    | v5_funct_1(k1_xboole_0,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2957,c_41,c_44,c_665,c_1292,c_1302,c_1635,c_2457])).

cnf(c_3026,plain,
    ( v5_funct_1(k1_xboole_0,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3025])).

cnf(c_21,negated_conjecture,
    ( ~ v5_funct_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1046,plain,
    ( v5_funct_1(k1_xboole_0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3032,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3026,c_1046])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_24,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3032,c_25,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.55/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/0.99  
% 2.55/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.55/0.99  
% 2.55/0.99  ------  iProver source info
% 2.55/0.99  
% 2.55/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.55/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.55/0.99  git: non_committed_changes: false
% 2.55/0.99  git: last_make_outside_of_git: false
% 2.55/0.99  
% 2.55/0.99  ------ 
% 2.55/0.99  
% 2.55/0.99  ------ Input Options
% 2.55/0.99  
% 2.55/0.99  --out_options                           all
% 2.55/0.99  --tptp_safe_out                         true
% 2.55/0.99  --problem_path                          ""
% 2.55/0.99  --include_path                          ""
% 2.55/0.99  --clausifier                            res/vclausify_rel
% 2.55/0.99  --clausifier_options                    --mode clausify
% 2.55/0.99  --stdin                                 false
% 2.55/0.99  --stats_out                             all
% 2.55/0.99  
% 2.55/0.99  ------ General Options
% 2.55/0.99  
% 2.55/0.99  --fof                                   false
% 2.55/0.99  --time_out_real                         305.
% 2.55/0.99  --time_out_virtual                      -1.
% 2.55/0.99  --symbol_type_check                     false
% 2.55/0.99  --clausify_out                          false
% 2.55/0.99  --sig_cnt_out                           false
% 2.55/0.99  --trig_cnt_out                          false
% 2.55/0.99  --trig_cnt_out_tolerance                1.
% 2.55/0.99  --trig_cnt_out_sk_spl                   false
% 2.55/0.99  --abstr_cl_out                          false
% 2.55/0.99  
% 2.55/0.99  ------ Global Options
% 2.55/0.99  
% 2.55/0.99  --schedule                              default
% 2.55/0.99  --add_important_lit                     false
% 2.55/0.99  --prop_solver_per_cl                    1000
% 2.55/0.99  --min_unsat_core                        false
% 2.55/0.99  --soft_assumptions                      false
% 2.55/0.99  --soft_lemma_size                       3
% 2.55/0.99  --prop_impl_unit_size                   0
% 2.55/0.99  --prop_impl_unit                        []
% 2.55/0.99  --share_sel_clauses                     true
% 2.55/0.99  --reset_solvers                         false
% 2.55/0.99  --bc_imp_inh                            [conj_cone]
% 2.55/0.99  --conj_cone_tolerance                   3.
% 2.55/0.99  --extra_neg_conj                        none
% 2.55/0.99  --large_theory_mode                     true
% 2.55/0.99  --prolific_symb_bound                   200
% 2.55/0.99  --lt_threshold                          2000
% 2.55/0.99  --clause_weak_htbl                      true
% 2.55/0.99  --gc_record_bc_elim                     false
% 2.55/0.99  
% 2.55/0.99  ------ Preprocessing Options
% 2.55/0.99  
% 2.55/0.99  --preprocessing_flag                    true
% 2.55/0.99  --time_out_prep_mult                    0.1
% 2.55/0.99  --splitting_mode                        input
% 2.55/0.99  --splitting_grd                         true
% 2.55/0.99  --splitting_cvd                         false
% 2.55/0.99  --splitting_cvd_svl                     false
% 2.55/0.99  --splitting_nvd                         32
% 2.55/0.99  --sub_typing                            true
% 2.55/0.99  --prep_gs_sim                           true
% 2.55/0.99  --prep_unflatten                        true
% 2.55/0.99  --prep_res_sim                          true
% 2.55/0.99  --prep_upred                            true
% 2.55/0.99  --prep_sem_filter                       exhaustive
% 2.55/0.99  --prep_sem_filter_out                   false
% 2.55/0.99  --pred_elim                             true
% 2.55/0.99  --res_sim_input                         true
% 2.55/0.99  --eq_ax_congr_red                       true
% 2.55/0.99  --pure_diseq_elim                       true
% 2.55/0.99  --brand_transform                       false
% 2.55/0.99  --non_eq_to_eq                          false
% 2.55/0.99  --prep_def_merge                        true
% 2.55/0.99  --prep_def_merge_prop_impl              false
% 2.55/0.99  --prep_def_merge_mbd                    true
% 2.55/0.99  --prep_def_merge_tr_red                 false
% 2.55/0.99  --prep_def_merge_tr_cl                  false
% 2.55/0.99  --smt_preprocessing                     true
% 2.55/0.99  --smt_ac_axioms                         fast
% 2.55/0.99  --preprocessed_out                      false
% 2.55/0.99  --preprocessed_stats                    false
% 2.55/0.99  
% 2.55/0.99  ------ Abstraction refinement Options
% 2.55/0.99  
% 2.55/0.99  --abstr_ref                             []
% 2.55/0.99  --abstr_ref_prep                        false
% 2.55/0.99  --abstr_ref_until_sat                   false
% 2.55/0.99  --abstr_ref_sig_restrict                funpre
% 2.55/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.55/0.99  --abstr_ref_under                       []
% 2.55/0.99  
% 2.55/0.99  ------ SAT Options
% 2.55/0.99  
% 2.55/0.99  --sat_mode                              false
% 2.55/0.99  --sat_fm_restart_options                ""
% 2.55/0.99  --sat_gr_def                            false
% 2.55/0.99  --sat_epr_types                         true
% 2.55/0.99  --sat_non_cyclic_types                  false
% 2.55/0.99  --sat_finite_models                     false
% 2.55/0.99  --sat_fm_lemmas                         false
% 2.55/0.99  --sat_fm_prep                           false
% 2.55/0.99  --sat_fm_uc_incr                        true
% 2.55/0.99  --sat_out_model                         small
% 2.55/0.99  --sat_out_clauses                       false
% 2.55/0.99  
% 2.55/0.99  ------ QBF Options
% 2.55/0.99  
% 2.55/0.99  --qbf_mode                              false
% 2.55/0.99  --qbf_elim_univ                         false
% 2.55/0.99  --qbf_dom_inst                          none
% 2.55/0.99  --qbf_dom_pre_inst                      false
% 2.55/0.99  --qbf_sk_in                             false
% 2.55/0.99  --qbf_pred_elim                         true
% 2.55/0.99  --qbf_split                             512
% 2.55/0.99  
% 2.55/0.99  ------ BMC1 Options
% 2.55/0.99  
% 2.55/0.99  --bmc1_incremental                      false
% 2.55/0.99  --bmc1_axioms                           reachable_all
% 2.55/0.99  --bmc1_min_bound                        0
% 2.55/0.99  --bmc1_max_bound                        -1
% 2.55/0.99  --bmc1_max_bound_default                -1
% 2.55/0.99  --bmc1_symbol_reachability              true
% 2.55/0.99  --bmc1_property_lemmas                  false
% 2.55/0.99  --bmc1_k_induction                      false
% 2.55/0.99  --bmc1_non_equiv_states                 false
% 2.55/0.99  --bmc1_deadlock                         false
% 2.55/0.99  --bmc1_ucm                              false
% 2.55/0.99  --bmc1_add_unsat_core                   none
% 2.55/0.99  --bmc1_unsat_core_children              false
% 2.55/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.55/0.99  --bmc1_out_stat                         full
% 2.55/0.99  --bmc1_ground_init                      false
% 2.55/0.99  --bmc1_pre_inst_next_state              false
% 2.55/0.99  --bmc1_pre_inst_state                   false
% 2.55/0.99  --bmc1_pre_inst_reach_state             false
% 2.55/0.99  --bmc1_out_unsat_core                   false
% 2.55/0.99  --bmc1_aig_witness_out                  false
% 2.55/0.99  --bmc1_verbose                          false
% 2.55/0.99  --bmc1_dump_clauses_tptp                false
% 2.55/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.55/0.99  --bmc1_dump_file                        -
% 2.55/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.55/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.55/0.99  --bmc1_ucm_extend_mode                  1
% 2.55/0.99  --bmc1_ucm_init_mode                    2
% 2.55/0.99  --bmc1_ucm_cone_mode                    none
% 2.55/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.55/0.99  --bmc1_ucm_relax_model                  4
% 2.55/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.55/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.55/0.99  --bmc1_ucm_layered_model                none
% 2.55/0.99  --bmc1_ucm_max_lemma_size               10
% 2.55/0.99  
% 2.55/0.99  ------ AIG Options
% 2.55/0.99  
% 2.55/0.99  --aig_mode                              false
% 2.55/0.99  
% 2.55/0.99  ------ Instantiation Options
% 2.55/0.99  
% 2.55/0.99  --instantiation_flag                    true
% 2.55/0.99  --inst_sos_flag                         false
% 2.55/0.99  --inst_sos_phase                        true
% 2.55/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.55/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.55/0.99  --inst_lit_sel_side                     num_symb
% 2.55/0.99  --inst_solver_per_active                1400
% 2.55/0.99  --inst_solver_calls_frac                1.
% 2.55/0.99  --inst_passive_queue_type               priority_queues
% 2.55/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.55/0.99  --inst_passive_queues_freq              [25;2]
% 2.55/0.99  --inst_dismatching                      true
% 2.55/0.99  --inst_eager_unprocessed_to_passive     true
% 2.55/0.99  --inst_prop_sim_given                   true
% 2.55/0.99  --inst_prop_sim_new                     false
% 2.55/0.99  --inst_subs_new                         false
% 2.55/0.99  --inst_eq_res_simp                      false
% 2.55/0.99  --inst_subs_given                       false
% 2.55/0.99  --inst_orphan_elimination               true
% 2.55/0.99  --inst_learning_loop_flag               true
% 2.55/0.99  --inst_learning_start                   3000
% 2.55/0.99  --inst_learning_factor                  2
% 2.55/0.99  --inst_start_prop_sim_after_learn       3
% 2.55/0.99  --inst_sel_renew                        solver
% 2.55/0.99  --inst_lit_activity_flag                true
% 2.55/0.99  --inst_restr_to_given                   false
% 2.55/0.99  --inst_activity_threshold               500
% 2.55/0.99  --inst_out_proof                        true
% 2.55/0.99  
% 2.55/0.99  ------ Resolution Options
% 2.55/0.99  
% 2.55/0.99  --resolution_flag                       true
% 2.55/0.99  --res_lit_sel                           adaptive
% 2.55/0.99  --res_lit_sel_side                      none
% 2.55/0.99  --res_ordering                          kbo
% 2.55/0.99  --res_to_prop_solver                    active
% 2.55/0.99  --res_prop_simpl_new                    false
% 2.55/0.99  --res_prop_simpl_given                  true
% 2.55/0.99  --res_passive_queue_type                priority_queues
% 2.55/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.55/0.99  --res_passive_queues_freq               [15;5]
% 2.55/0.99  --res_forward_subs                      full
% 2.55/0.99  --res_backward_subs                     full
% 2.55/0.99  --res_forward_subs_resolution           true
% 2.55/0.99  --res_backward_subs_resolution          true
% 2.55/0.99  --res_orphan_elimination                true
% 2.55/0.99  --res_time_limit                        2.
% 2.55/0.99  --res_out_proof                         true
% 2.55/0.99  
% 2.55/0.99  ------ Superposition Options
% 2.55/0.99  
% 2.55/0.99  --superposition_flag                    true
% 2.55/0.99  --sup_passive_queue_type                priority_queues
% 2.55/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.55/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.55/0.99  --demod_completeness_check              fast
% 2.55/0.99  --demod_use_ground                      true
% 2.55/0.99  --sup_to_prop_solver                    passive
% 2.55/0.99  --sup_prop_simpl_new                    true
% 2.55/0.99  --sup_prop_simpl_given                  true
% 2.55/0.99  --sup_fun_splitting                     false
% 2.55/0.99  --sup_smt_interval                      50000
% 2.55/0.99  
% 2.55/0.99  ------ Superposition Simplification Setup
% 2.55/0.99  
% 2.55/0.99  --sup_indices_passive                   []
% 2.55/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.55/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/0.99  --sup_full_bw                           [BwDemod]
% 2.55/0.99  --sup_immed_triv                        [TrivRules]
% 2.55/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.55/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/0.99  --sup_immed_bw_main                     []
% 2.55/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.55/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/0.99  
% 2.55/0.99  ------ Combination Options
% 2.55/0.99  
% 2.55/0.99  --comb_res_mult                         3
% 2.55/0.99  --comb_sup_mult                         2
% 2.55/0.99  --comb_inst_mult                        10
% 2.55/0.99  
% 2.55/0.99  ------ Debug Options
% 2.55/0.99  
% 2.55/0.99  --dbg_backtrace                         false
% 2.55/0.99  --dbg_dump_prop_clauses                 false
% 2.55/0.99  --dbg_dump_prop_clauses_file            -
% 2.55/0.99  --dbg_out_stat                          false
% 2.55/0.99  ------ Parsing...
% 2.55/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.55/0.99  
% 2.55/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.55/0.99  
% 2.55/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.55/0.99  
% 2.55/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.55/0.99  ------ Proving...
% 2.55/0.99  ------ Problem Properties 
% 2.55/0.99  
% 2.55/0.99  
% 2.55/0.99  clauses                                 23
% 2.55/0.99  conjectures                             3
% 2.55/0.99  EPR                                     3
% 2.55/0.99  Horn                                    20
% 2.55/0.99  unary                                   6
% 2.55/0.99  binary                                  9
% 2.55/0.99  lits                                    61
% 2.55/0.99  lits eq                                 16
% 2.55/0.99  fd_pure                                 0
% 2.55/0.99  fd_pseudo                               0
% 2.55/0.99  fd_cond                                 0
% 2.55/0.99  fd_pseudo_cond                          0
% 2.55/0.99  AC symbols                              0
% 2.55/0.99  
% 2.55/0.99  ------ Schedule dynamic 5 is on 
% 2.55/0.99  
% 2.55/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.55/0.99  
% 2.55/0.99  
% 2.55/0.99  ------ 
% 2.55/0.99  Current options:
% 2.55/0.99  ------ 
% 2.55/0.99  
% 2.55/0.99  ------ Input Options
% 2.55/0.99  
% 2.55/0.99  --out_options                           all
% 2.55/0.99  --tptp_safe_out                         true
% 2.55/0.99  --problem_path                          ""
% 2.55/0.99  --include_path                          ""
% 2.55/0.99  --clausifier                            res/vclausify_rel
% 2.55/0.99  --clausifier_options                    --mode clausify
% 2.55/0.99  --stdin                                 false
% 2.55/0.99  --stats_out                             all
% 2.55/0.99  
% 2.55/0.99  ------ General Options
% 2.55/0.99  
% 2.55/0.99  --fof                                   false
% 2.55/0.99  --time_out_real                         305.
% 2.55/0.99  --time_out_virtual                      -1.
% 2.55/0.99  --symbol_type_check                     false
% 2.55/0.99  --clausify_out                          false
% 2.55/0.99  --sig_cnt_out                           false
% 2.55/0.99  --trig_cnt_out                          false
% 2.55/0.99  --trig_cnt_out_tolerance                1.
% 2.55/0.99  --trig_cnt_out_sk_spl                   false
% 2.55/0.99  --abstr_cl_out                          false
% 2.55/0.99  
% 2.55/0.99  ------ Global Options
% 2.55/0.99  
% 2.55/0.99  --schedule                              default
% 2.55/0.99  --add_important_lit                     false
% 2.55/0.99  --prop_solver_per_cl                    1000
% 2.55/0.99  --min_unsat_core                        false
% 2.55/0.99  --soft_assumptions                      false
% 2.55/0.99  --soft_lemma_size                       3
% 2.55/0.99  --prop_impl_unit_size                   0
% 2.55/0.99  --prop_impl_unit                        []
% 2.55/0.99  --share_sel_clauses                     true
% 2.55/0.99  --reset_solvers                         false
% 2.55/0.99  --bc_imp_inh                            [conj_cone]
% 2.55/0.99  --conj_cone_tolerance                   3.
% 2.55/0.99  --extra_neg_conj                        none
% 2.55/0.99  --large_theory_mode                     true
% 2.55/0.99  --prolific_symb_bound                   200
% 2.55/0.99  --lt_threshold                          2000
% 2.55/0.99  --clause_weak_htbl                      true
% 2.55/0.99  --gc_record_bc_elim                     false
% 2.55/0.99  
% 2.55/0.99  ------ Preprocessing Options
% 2.55/0.99  
% 2.55/0.99  --preprocessing_flag                    true
% 2.55/0.99  --time_out_prep_mult                    0.1
% 2.55/0.99  --splitting_mode                        input
% 2.55/0.99  --splitting_grd                         true
% 2.55/0.99  --splitting_cvd                         false
% 2.55/0.99  --splitting_cvd_svl                     false
% 2.55/0.99  --splitting_nvd                         32
% 2.55/0.99  --sub_typing                            true
% 2.55/0.99  --prep_gs_sim                           true
% 2.55/0.99  --prep_unflatten                        true
% 2.55/0.99  --prep_res_sim                          true
% 2.55/0.99  --prep_upred                            true
% 2.55/0.99  --prep_sem_filter                       exhaustive
% 2.55/0.99  --prep_sem_filter_out                   false
% 2.55/0.99  --pred_elim                             true
% 2.55/0.99  --res_sim_input                         true
% 2.55/0.99  --eq_ax_congr_red                       true
% 2.55/0.99  --pure_diseq_elim                       true
% 2.55/0.99  --brand_transform                       false
% 2.55/0.99  --non_eq_to_eq                          false
% 2.55/0.99  --prep_def_merge                        true
% 2.55/0.99  --prep_def_merge_prop_impl              false
% 2.55/0.99  --prep_def_merge_mbd                    true
% 2.55/0.99  --prep_def_merge_tr_red                 false
% 2.55/0.99  --prep_def_merge_tr_cl                  false
% 2.55/0.99  --smt_preprocessing                     true
% 2.55/0.99  --smt_ac_axioms                         fast
% 2.55/0.99  --preprocessed_out                      false
% 2.55/0.99  --preprocessed_stats                    false
% 2.55/0.99  
% 2.55/0.99  ------ Abstraction refinement Options
% 2.55/0.99  
% 2.55/0.99  --abstr_ref                             []
% 2.55/0.99  --abstr_ref_prep                        false
% 2.55/0.99  --abstr_ref_until_sat                   false
% 2.55/0.99  --abstr_ref_sig_restrict                funpre
% 2.55/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.55/0.99  --abstr_ref_under                       []
% 2.55/0.99  
% 2.55/0.99  ------ SAT Options
% 2.55/0.99  
% 2.55/0.99  --sat_mode                              false
% 2.55/0.99  --sat_fm_restart_options                ""
% 2.55/0.99  --sat_gr_def                            false
% 2.55/0.99  --sat_epr_types                         true
% 2.55/0.99  --sat_non_cyclic_types                  false
% 2.55/0.99  --sat_finite_models                     false
% 2.55/0.99  --sat_fm_lemmas                         false
% 2.55/0.99  --sat_fm_prep                           false
% 2.55/0.99  --sat_fm_uc_incr                        true
% 2.55/0.99  --sat_out_model                         small
% 2.55/0.99  --sat_out_clauses                       false
% 2.55/0.99  
% 2.55/0.99  ------ QBF Options
% 2.55/0.99  
% 2.55/0.99  --qbf_mode                              false
% 2.55/0.99  --qbf_elim_univ                         false
% 2.55/0.99  --qbf_dom_inst                          none
% 2.55/0.99  --qbf_dom_pre_inst                      false
% 2.55/0.99  --qbf_sk_in                             false
% 2.55/0.99  --qbf_pred_elim                         true
% 2.55/0.99  --qbf_split                             512
% 2.55/0.99  
% 2.55/0.99  ------ BMC1 Options
% 2.55/0.99  
% 2.55/0.99  --bmc1_incremental                      false
% 2.55/0.99  --bmc1_axioms                           reachable_all
% 2.55/0.99  --bmc1_min_bound                        0
% 2.55/0.99  --bmc1_max_bound                        -1
% 2.55/0.99  --bmc1_max_bound_default                -1
% 2.55/0.99  --bmc1_symbol_reachability              true
% 2.55/0.99  --bmc1_property_lemmas                  false
% 2.55/0.99  --bmc1_k_induction                      false
% 2.55/0.99  --bmc1_non_equiv_states                 false
% 2.55/0.99  --bmc1_deadlock                         false
% 2.55/0.99  --bmc1_ucm                              false
% 2.55/0.99  --bmc1_add_unsat_core                   none
% 2.55/0.99  --bmc1_unsat_core_children              false
% 2.55/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.55/0.99  --bmc1_out_stat                         full
% 2.55/0.99  --bmc1_ground_init                      false
% 2.55/0.99  --bmc1_pre_inst_next_state              false
% 2.55/0.99  --bmc1_pre_inst_state                   false
% 2.55/0.99  --bmc1_pre_inst_reach_state             false
% 2.55/0.99  --bmc1_out_unsat_core                   false
% 2.55/0.99  --bmc1_aig_witness_out                  false
% 2.55/0.99  --bmc1_verbose                          false
% 2.55/0.99  --bmc1_dump_clauses_tptp                false
% 2.55/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.55/0.99  --bmc1_dump_file                        -
% 2.55/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.55/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.55/0.99  --bmc1_ucm_extend_mode                  1
% 2.55/0.99  --bmc1_ucm_init_mode                    2
% 2.55/0.99  --bmc1_ucm_cone_mode                    none
% 2.55/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.55/0.99  --bmc1_ucm_relax_model                  4
% 2.55/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.55/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.55/0.99  --bmc1_ucm_layered_model                none
% 2.55/0.99  --bmc1_ucm_max_lemma_size               10
% 2.55/0.99  
% 2.55/0.99  ------ AIG Options
% 2.55/0.99  
% 2.55/0.99  --aig_mode                              false
% 2.55/0.99  
% 2.55/0.99  ------ Instantiation Options
% 2.55/0.99  
% 2.55/0.99  --instantiation_flag                    true
% 2.55/0.99  --inst_sos_flag                         false
% 2.55/0.99  --inst_sos_phase                        true
% 2.55/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.55/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.55/0.99  --inst_lit_sel_side                     none
% 2.55/0.99  --inst_solver_per_active                1400
% 2.55/0.99  --inst_solver_calls_frac                1.
% 2.55/0.99  --inst_passive_queue_type               priority_queues
% 2.55/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.55/0.99  --inst_passive_queues_freq              [25;2]
% 2.55/0.99  --inst_dismatching                      true
% 2.55/0.99  --inst_eager_unprocessed_to_passive     true
% 2.55/0.99  --inst_prop_sim_given                   true
% 2.55/0.99  --inst_prop_sim_new                     false
% 2.55/0.99  --inst_subs_new                         false
% 2.55/0.99  --inst_eq_res_simp                      false
% 2.55/0.99  --inst_subs_given                       false
% 2.55/0.99  --inst_orphan_elimination               true
% 2.55/0.99  --inst_learning_loop_flag               true
% 2.55/0.99  --inst_learning_start                   3000
% 2.55/0.99  --inst_learning_factor                  2
% 2.55/0.99  --inst_start_prop_sim_after_learn       3
% 2.55/0.99  --inst_sel_renew                        solver
% 2.55/0.99  --inst_lit_activity_flag                true
% 2.55/0.99  --inst_restr_to_given                   false
% 2.55/0.99  --inst_activity_threshold               500
% 2.55/0.99  --inst_out_proof                        true
% 2.55/0.99  
% 2.55/0.99  ------ Resolution Options
% 2.55/0.99  
% 2.55/0.99  --resolution_flag                       false
% 2.55/0.99  --res_lit_sel                           adaptive
% 2.55/0.99  --res_lit_sel_side                      none
% 2.55/0.99  --res_ordering                          kbo
% 2.55/0.99  --res_to_prop_solver                    active
% 2.55/0.99  --res_prop_simpl_new                    false
% 2.55/0.99  --res_prop_simpl_given                  true
% 2.55/0.99  --res_passive_queue_type                priority_queues
% 2.55/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.55/0.99  --res_passive_queues_freq               [15;5]
% 2.55/0.99  --res_forward_subs                      full
% 2.55/0.99  --res_backward_subs                     full
% 2.55/0.99  --res_forward_subs_resolution           true
% 2.55/0.99  --res_backward_subs_resolution          true
% 2.55/0.99  --res_orphan_elimination                true
% 2.55/0.99  --res_time_limit                        2.
% 2.55/0.99  --res_out_proof                         true
% 2.55/0.99  
% 2.55/0.99  ------ Superposition Options
% 2.55/0.99  
% 2.55/0.99  --superposition_flag                    true
% 2.55/0.99  --sup_passive_queue_type                priority_queues
% 2.55/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.55/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.55/0.99  --demod_completeness_check              fast
% 2.55/0.99  --demod_use_ground                      true
% 2.55/0.99  --sup_to_prop_solver                    passive
% 2.55/0.99  --sup_prop_simpl_new                    true
% 2.55/0.99  --sup_prop_simpl_given                  true
% 2.55/0.99  --sup_fun_splitting                     false
% 2.55/0.99  --sup_smt_interval                      50000
% 2.55/0.99  
% 2.55/0.99  ------ Superposition Simplification Setup
% 2.55/0.99  
% 2.55/0.99  --sup_indices_passive                   []
% 2.55/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.55/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/0.99  --sup_full_bw                           [BwDemod]
% 2.55/0.99  --sup_immed_triv                        [TrivRules]
% 2.55/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.55/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/0.99  --sup_immed_bw_main                     []
% 2.55/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.55/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/0.99  
% 2.55/0.99  ------ Combination Options
% 2.55/0.99  
% 2.55/0.99  --comb_res_mult                         3
% 2.55/0.99  --comb_sup_mult                         2
% 2.55/0.99  --comb_inst_mult                        10
% 2.55/0.99  
% 2.55/0.99  ------ Debug Options
% 2.55/0.99  
% 2.55/0.99  --dbg_backtrace                         false
% 2.55/0.99  --dbg_dump_prop_clauses                 false
% 2.55/0.99  --dbg_dump_prop_clauses_file            -
% 2.55/0.99  --dbg_out_stat                          false
% 2.55/0.99  
% 2.55/0.99  
% 2.55/0.99  
% 2.55/0.99  
% 2.55/0.99  ------ Proving...
% 2.55/0.99  
% 2.55/0.99  
% 2.55/0.99  % SZS status Theorem for theBenchmark.p
% 2.55/0.99  
% 2.55/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.55/0.99  
% 2.55/0.99  fof(f11,axiom,(
% 2.55/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 2.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.99  
% 2.55/0.99  fof(f25,plain,(
% 2.55/0.99    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.55/0.99    inference(ennf_transformation,[],[f11])).
% 2.55/0.99  
% 2.55/0.99  fof(f26,plain,(
% 2.55/0.99    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.55/0.99    inference(flattening,[],[f25])).
% 2.55/0.99  
% 2.55/0.99  fof(f32,plain,(
% 2.55/0.99    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.55/0.99    inference(nnf_transformation,[],[f26])).
% 2.55/0.99  
% 2.55/0.99  fof(f33,plain,(
% 2.55/0.99    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.55/0.99    inference(rectify,[],[f32])).
% 2.55/0.99  
% 2.55/0.99  fof(f34,plain,(
% 2.55/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1))) => (~r2_hidden(k1_funct_1(X1,sK0(X0,X1)),k1_funct_1(X0,sK0(X0,X1))) & r2_hidden(sK0(X0,X1),k1_relat_1(X1))))),
% 2.55/0.99    introduced(choice_axiom,[])).
% 2.55/0.99  
% 2.55/0.99  fof(f35,plain,(
% 2.55/0.99    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | (~r2_hidden(k1_funct_1(X1,sK0(X0,X1)),k1_funct_1(X0,sK0(X0,X1))) & r2_hidden(sK0(X0,X1),k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.55/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 2.55/0.99  
% 2.55/0.99  fof(f56,plain,(
% 2.55/0.99    ( ! [X0,X1] : (v5_funct_1(X1,X0) | r2_hidden(sK0(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.55/0.99    inference(cnf_transformation,[],[f35])).
% 2.55/0.99  
% 2.55/0.99  fof(f12,axiom,(
% 2.55/0.99    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.99  
% 2.55/0.99  fof(f58,plain,(
% 2.55/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.55/0.99    inference(cnf_transformation,[],[f12])).
% 2.55/0.99  
% 2.55/0.99  fof(f3,axiom,(
% 2.55/0.99    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 2.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.99  
% 2.55/0.99  fof(f17,plain,(
% 2.55/0.99    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 2.55/0.99    inference(ennf_transformation,[],[f3])).
% 2.55/0.99  
% 2.55/0.99  fof(f45,plain,(
% 2.55/0.99    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 2.55/0.99    inference(cnf_transformation,[],[f17])).
% 2.55/0.99  
% 2.55/0.99  fof(f10,axiom,(
% 2.55/0.99    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 2.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.99  
% 2.55/0.99  fof(f24,plain,(
% 2.55/0.99    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.55/0.99    inference(ennf_transformation,[],[f10])).
% 2.55/0.99  
% 2.55/0.99  fof(f54,plain,(
% 2.55/0.99    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 2.55/0.99    inference(cnf_transformation,[],[f24])).
% 2.55/0.99  
% 2.55/0.99  fof(f13,axiom,(
% 2.55/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 2.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.99  
% 2.55/0.99  fof(f27,plain,(
% 2.55/0.99    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.55/0.99    inference(ennf_transformation,[],[f13])).
% 2.55/0.99  
% 2.55/0.99  fof(f28,plain,(
% 2.55/0.99    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.55/0.99    inference(flattening,[],[f27])).
% 2.55/0.99  
% 2.55/0.99  fof(f36,plain,(
% 2.55/0.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.55/0.99    inference(nnf_transformation,[],[f28])).
% 2.55/0.99  
% 2.55/0.99  fof(f37,plain,(
% 2.55/0.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.55/0.99    inference(flattening,[],[f36])).
% 2.55/0.99  
% 2.55/0.99  fof(f38,plain,(
% 2.55/0.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.55/0.99    inference(rectify,[],[f37])).
% 2.55/0.99  
% 2.55/0.99  fof(f39,plain,(
% 2.55/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK1(X0,X1)) != sK1(X0,X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.55/0.99    introduced(choice_axiom,[])).
% 2.55/0.99  
% 2.55/0.99  fof(f40,plain,(
% 2.55/0.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK1(X0,X1)) != sK1(X0,X1) & r2_hidden(sK1(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.55/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 2.55/0.99  
% 2.55/0.99  fof(f60,plain,(
% 2.55/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | k6_relat_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.55/0.99    inference(cnf_transformation,[],[f40])).
% 2.55/0.99  
% 2.55/0.99  fof(f70,plain,(
% 2.55/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0 | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.55/0.99    inference(equality_resolution,[],[f60])).
% 2.55/0.99  
% 2.55/0.99  fof(f59,plain,(
% 2.55/0.99    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.55/0.99    inference(cnf_transformation,[],[f12])).
% 2.55/0.99  
% 2.55/0.99  fof(f1,axiom,(
% 2.55/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 2.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.99  
% 2.55/0.99  fof(f16,plain,(
% 2.55/0.99    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 2.55/0.99    inference(ennf_transformation,[],[f1])).
% 2.55/0.99  
% 2.55/0.99  fof(f43,plain,(
% 2.55/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 2.55/0.99    inference(cnf_transformation,[],[f16])).
% 2.55/0.99  
% 2.55/0.99  fof(f5,axiom,(
% 2.55/0.99    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.99  
% 2.55/0.99  fof(f19,plain,(
% 2.55/0.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.55/0.99    inference(ennf_transformation,[],[f5])).
% 2.55/0.99  
% 2.55/0.99  fof(f47,plain,(
% 2.55/0.99    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.55/0.99    inference(cnf_transformation,[],[f19])).
% 2.55/0.99  
% 2.55/0.99  fof(f9,axiom,(
% 2.55/0.99    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.99  
% 2.55/0.99  fof(f23,plain,(
% 2.55/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.55/0.99    inference(ennf_transformation,[],[f9])).
% 2.55/0.99  
% 2.55/0.99  fof(f53,plain,(
% 2.55/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 2.55/0.99    inference(cnf_transformation,[],[f23])).
% 2.55/0.99  
% 2.55/0.99  fof(f8,axiom,(
% 2.55/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 2.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.99  
% 2.55/0.99  fof(f22,plain,(
% 2.55/0.99    ! [X0] : ((k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0))),
% 2.55/0.99    inference(ennf_transformation,[],[f8])).
% 2.55/0.99  
% 2.55/0.99  fof(f52,plain,(
% 2.55/0.99    ( ! [X0] : (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 2.55/0.99    inference(cnf_transformation,[],[f22])).
% 2.55/0.99  
% 2.55/0.99  fof(f14,conjecture,(
% 2.55/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 2.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.99  
% 2.55/0.99  fof(f15,negated_conjecture,(
% 2.55/0.99    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 2.55/0.99    inference(negated_conjecture,[],[f14])).
% 2.55/0.99  
% 2.55/0.99  fof(f29,plain,(
% 2.55/0.99    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.55/0.99    inference(ennf_transformation,[],[f15])).
% 2.55/0.99  
% 2.55/0.99  fof(f30,plain,(
% 2.55/0.99    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.55/0.99    inference(flattening,[],[f29])).
% 2.55/0.99  
% 2.55/0.99  fof(f41,plain,(
% 2.55/0.99    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v5_funct_1(k1_xboole_0,sK2) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 2.55/0.99    introduced(choice_axiom,[])).
% 2.55/0.99  
% 2.55/0.99  fof(f42,plain,(
% 2.55/0.99    ~v5_funct_1(k1_xboole_0,sK2) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 2.55/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f41])).
% 2.55/0.99  
% 2.55/0.99  fof(f64,plain,(
% 2.55/0.99    v1_relat_1(sK2)),
% 2.55/0.99    inference(cnf_transformation,[],[f42])).
% 2.55/0.99  
% 2.55/0.99  fof(f6,axiom,(
% 2.55/0.99    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_xboole_0) = k1_xboole_0)),
% 2.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.00  
% 2.55/1.00  fof(f20,plain,(
% 2.55/1.00    ! [X0] : (k9_relat_1(X0,k1_xboole_0) = k1_xboole_0 | ~v1_relat_1(X0))),
% 2.55/1.00    inference(ennf_transformation,[],[f6])).
% 2.55/1.00  
% 2.55/1.00  fof(f48,plain,(
% 2.55/1.00    ( ! [X0] : (k9_relat_1(X0,k1_xboole_0) = k1_xboole_0 | ~v1_relat_1(X0)) )),
% 2.55/1.00    inference(cnf_transformation,[],[f20])).
% 2.55/1.00  
% 2.55/1.00  fof(f7,axiom,(
% 2.55/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k11_relat_1(X1,X0) != k1_xboole_0))),
% 2.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.00  
% 2.55/1.00  fof(f21,plain,(
% 2.55/1.00    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k11_relat_1(X1,X0) != k1_xboole_0) | ~v1_relat_1(X1))),
% 2.55/1.00    inference(ennf_transformation,[],[f7])).
% 2.55/1.00  
% 2.55/1.00  fof(f31,plain,(
% 2.55/1.00    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k1_xboole_0) & (k11_relat_1(X1,X0) != k1_xboole_0 | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 2.55/1.00    inference(nnf_transformation,[],[f21])).
% 2.55/1.00  
% 2.55/1.00  fof(f49,plain,(
% 2.55/1.00    ( ! [X0,X1] : (k11_relat_1(X1,X0) != k1_xboole_0 | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.55/1.00    inference(cnf_transformation,[],[f31])).
% 2.55/1.00  
% 2.55/1.00  fof(f66,plain,(
% 2.55/1.00    ~v5_funct_1(k1_xboole_0,sK2)),
% 2.55/1.00    inference(cnf_transformation,[],[f42])).
% 2.55/1.00  
% 2.55/1.00  fof(f65,plain,(
% 2.55/1.00    v1_funct_1(sK2)),
% 2.55/1.00    inference(cnf_transformation,[],[f42])).
% 2.55/1.00  
% 2.55/1.00  cnf(c_13,plain,
% 2.55/1.00      ( v5_funct_1(X0,X1)
% 2.55/1.00      | r2_hidden(sK0(X1,X0),k1_relat_1(X0))
% 2.55/1.00      | ~ v1_funct_1(X0)
% 2.55/1.00      | ~ v1_funct_1(X1)
% 2.55/1.00      | ~ v1_relat_1(X1)
% 2.55/1.00      | ~ v1_relat_1(X0) ),
% 2.55/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1052,plain,
% 2.55/1.00      ( v5_funct_1(X0,X1) = iProver_top
% 2.55/1.00      | r2_hidden(sK0(X1,X0),k1_relat_1(X0)) = iProver_top
% 2.55/1.00      | v1_funct_1(X0) != iProver_top
% 2.55/1.00      | v1_funct_1(X1) != iProver_top
% 2.55/1.00      | v1_relat_1(X0) != iProver_top
% 2.55/1.00      | v1_relat_1(X1) != iProver_top ),
% 2.55/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_16,plain,
% 2.55/1.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.55/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1064,plain,
% 2.55/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.55/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_2,plain,
% 2.55/1.00      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.55/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1063,plain,
% 2.55/1.00      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 2.55/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.55/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1516,plain,
% 2.55/1.00      ( k7_relat_1(k6_relat_1(X0),k1_xboole_0) = k1_xboole_0 ),
% 2.55/1.00      inference(superposition,[status(thm)],[c_1064,c_1063]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_11,plain,
% 2.55/1.00      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 2.55/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1054,plain,
% 2.55/1.00      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 2.55/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.55/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1647,plain,
% 2.55/1.00      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k6_relat_1(X0) ),
% 2.55/1.00      inference(superposition,[status(thm)],[c_1064,c_1054]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_20,plain,
% 2.55/1.00      ( ~ v1_funct_1(k6_relat_1(X0))
% 2.55/1.00      | ~ v1_relat_1(k6_relat_1(X0))
% 2.55/1.00      | k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.55/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_15,plain,
% 2.55/1.00      ( v1_funct_1(k6_relat_1(X0)) ),
% 2.55/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_138,plain,
% 2.55/1.00      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.55/1.00      inference(global_propositional_subsumption,
% 2.55/1.00                [status(thm)],
% 2.55/1.00                [c_20,c_16,c_15]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1652,plain,
% 2.55/1.00      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 2.55/1.00      inference(light_normalisation,[status(thm)],[c_1647,c_138]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_2457,plain,
% 2.55/1.00      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.55/1.00      inference(superposition,[status(thm)],[c_1516,c_1652]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_2634,plain,
% 2.55/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.55/1.00      inference(superposition,[status(thm)],[c_2457,c_1064]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_0,plain,
% 2.55/1.00      ( ~ v1_relat_1(X0)
% 2.55/1.00      | k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) ),
% 2.55/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1065,plain,
% 2.55/1.00      ( k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1)
% 2.55/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.55/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_2656,plain,
% 2.55/1.00      ( k9_relat_1(k1_xboole_0,k1_tarski(X0)) = k11_relat_1(k1_xboole_0,X0) ),
% 2.55/1.00      inference(superposition,[status(thm)],[c_2634,c_1065]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_4,plain,
% 2.55/1.00      ( ~ v1_relat_1(X0)
% 2.55/1.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.55/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1061,plain,
% 2.55/1.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.55/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.55/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_2657,plain,
% 2.55/1.00      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
% 2.55/1.00      inference(superposition,[status(thm)],[c_2634,c_1061]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_10,plain,
% 2.55/1.00      ( ~ v1_relat_1(X0)
% 2.55/1.00      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 2.55/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1055,plain,
% 2.55/1.00      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 2.55/1.00      | v1_relat_1(X1) != iProver_top ),
% 2.55/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_2664,plain,
% 2.55/1.00      ( k5_relat_1(k6_relat_1(X0),k1_xboole_0) = k7_relat_1(k1_xboole_0,X0) ),
% 2.55/1.00      inference(superposition,[status(thm)],[c_2634,c_1055]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_8,plain,
% 2.55/1.00      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.55/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1057,plain,
% 2.55/1.00      ( k5_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 2.55/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.55/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1467,plain,
% 2.55/1.00      ( k5_relat_1(k6_relat_1(X0),k1_xboole_0) = k1_xboole_0 ),
% 2.55/1.00      inference(superposition,[status(thm)],[c_1064,c_1057]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_2666,plain,
% 2.55/1.00      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.55/1.00      inference(light_normalisation,[status(thm)],[c_2664,c_1467]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_2671,plain,
% 2.55/1.00      ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
% 2.55/1.00      inference(light_normalisation,[status(thm)],[c_2657,c_2666]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_23,negated_conjecture,
% 2.55/1.00      ( v1_relat_1(sK2) ),
% 2.55/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1044,plain,
% 2.55/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 2.55/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1517,plain,
% 2.55/1.00      ( k7_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 2.55/1.00      inference(superposition,[status(thm)],[c_1044,c_1063]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_2077,plain,
% 2.55/1.00      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 2.55/1.00      inference(superposition,[status(thm)],[c_1044,c_1061]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_2280,plain,
% 2.55/1.00      ( k9_relat_1(sK2,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 2.55/1.00      inference(superposition,[status(thm)],[c_1517,c_2077]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_5,plain,
% 2.55/1.00      ( ~ v1_relat_1(X0) | k9_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.55/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1060,plain,
% 2.55/1.00      ( k9_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 2.55/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.55/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1507,plain,
% 2.55/1.00      ( k9_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 2.55/1.00      inference(superposition,[status(thm)],[c_1044,c_1060]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_2283,plain,
% 2.55/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.55/1.00      inference(light_normalisation,[status(thm)],[c_2280,c_1507]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_2673,plain,
% 2.55/1.00      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.55/1.00      inference(light_normalisation,[status(thm)],[c_2671,c_2283]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_2675,plain,
% 2.55/1.00      ( k11_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.55/1.00      inference(demodulation,[status(thm)],[c_2656,c_2673]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_7,plain,
% 2.55/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.55/1.00      | ~ v1_relat_1(X1)
% 2.55/1.00      | k11_relat_1(X1,X0) != k1_xboole_0 ),
% 2.55/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1058,plain,
% 2.55/1.00      ( k11_relat_1(X0,X1) != k1_xboole_0
% 2.55/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.55/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.55/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_2945,plain,
% 2.55/1.00      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 2.55/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.55/1.00      inference(superposition,[status(thm)],[c_2675,c_1058]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_39,plain,
% 2.55/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.55/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_41,plain,
% 2.55/1.00      ( v1_relat_1(k6_relat_1(k1_xboole_0)) = iProver_top ),
% 2.55/1.00      inference(instantiation,[status(thm)],[c_39]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_638,plain,( X0 = X0 ),theory(equality) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_665,plain,
% 2.55/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 2.55/1.00      inference(instantiation,[status(thm)],[c_638]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_641,plain,
% 2.55/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 2.55/1.00      theory(equality) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1289,plain,
% 2.55/1.00      ( v1_relat_1(X0)
% 2.55/1.00      | ~ v1_relat_1(k6_relat_1(X1))
% 2.55/1.00      | X0 != k6_relat_1(X1) ),
% 2.55/1.00      inference(instantiation,[status(thm)],[c_641]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1290,plain,
% 2.55/1.00      ( X0 != k6_relat_1(X1)
% 2.55/1.00      | v1_relat_1(X0) = iProver_top
% 2.55/1.00      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 2.55/1.00      inference(predicate_to_equality,[status(thm)],[c_1289]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1292,plain,
% 2.55/1.00      ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
% 2.55/1.00      | v1_relat_1(k6_relat_1(k1_xboole_0)) != iProver_top
% 2.55/1.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.55/1.00      inference(instantiation,[status(thm)],[c_1290]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_639,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1634,plain,
% 2.55/1.00      ( X0 != X1 | X0 = k6_relat_1(X2) | k6_relat_1(X2) != X1 ),
% 2.55/1.00      inference(instantiation,[status(thm)],[c_639]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1635,plain,
% 2.55/1.00      ( k6_relat_1(k1_xboole_0) != k1_xboole_0
% 2.55/1.00      | k1_xboole_0 = k6_relat_1(k1_xboole_0)
% 2.55/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.55/1.00      inference(instantiation,[status(thm)],[c_1634]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_2950,plain,
% 2.55/1.00      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 2.55/1.00      inference(global_propositional_subsumption,
% 2.55/1.00                [status(thm)],
% 2.55/1.00                [c_2945,c_41,c_665,c_1292,c_1635,c_2457]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_2957,plain,
% 2.55/1.00      ( v5_funct_1(k1_xboole_0,X0) = iProver_top
% 2.55/1.00      | v1_funct_1(X0) != iProver_top
% 2.55/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 2.55/1.00      | v1_relat_1(X0) != iProver_top
% 2.55/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.55/1.00      inference(superposition,[status(thm)],[c_1052,c_2950]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_42,plain,
% 2.55/1.00      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 2.55/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_44,plain,
% 2.55/1.00      ( v1_funct_1(k6_relat_1(k1_xboole_0)) = iProver_top ),
% 2.55/1.00      inference(instantiation,[status(thm)],[c_42]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_650,plain,
% 2.55/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 2.55/1.00      theory(equality) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1299,plain,
% 2.55/1.00      ( v1_funct_1(X0)
% 2.55/1.00      | ~ v1_funct_1(k6_relat_1(X1))
% 2.55/1.00      | X0 != k6_relat_1(X1) ),
% 2.55/1.00      inference(instantiation,[status(thm)],[c_650]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1300,plain,
% 2.55/1.00      ( X0 != k6_relat_1(X1)
% 2.55/1.00      | v1_funct_1(X0) = iProver_top
% 2.55/1.00      | v1_funct_1(k6_relat_1(X1)) != iProver_top ),
% 2.55/1.00      inference(predicate_to_equality,[status(thm)],[c_1299]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1302,plain,
% 2.55/1.00      ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
% 2.55/1.00      | v1_funct_1(k6_relat_1(k1_xboole_0)) != iProver_top
% 2.55/1.00      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 2.55/1.00      inference(instantiation,[status(thm)],[c_1300]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_3025,plain,
% 2.55/1.00      ( v1_relat_1(X0) != iProver_top
% 2.55/1.00      | v5_funct_1(k1_xboole_0,X0) = iProver_top
% 2.55/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.55/1.00      inference(global_propositional_subsumption,
% 2.55/1.00                [status(thm)],
% 2.55/1.00                [c_2957,c_41,c_44,c_665,c_1292,c_1302,c_1635,c_2457]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_3026,plain,
% 2.55/1.00      ( v5_funct_1(k1_xboole_0,X0) = iProver_top
% 2.55/1.00      | v1_funct_1(X0) != iProver_top
% 2.55/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.55/1.00      inference(renaming,[status(thm)],[c_3025]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_21,negated_conjecture,
% 2.55/1.00      ( ~ v5_funct_1(k1_xboole_0,sK2) ),
% 2.55/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_1046,plain,
% 2.55/1.00      ( v5_funct_1(k1_xboole_0,sK2) != iProver_top ),
% 2.55/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_3032,plain,
% 2.55/1.00      ( v1_funct_1(sK2) != iProver_top | v1_relat_1(sK2) != iProver_top ),
% 2.55/1.00      inference(superposition,[status(thm)],[c_3026,c_1046]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_22,negated_conjecture,
% 2.55/1.00      ( v1_funct_1(sK2) ),
% 2.55/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_25,plain,
% 2.55/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.55/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(c_24,plain,
% 2.55/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 2.55/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.55/1.00  
% 2.55/1.00  cnf(contradiction,plain,
% 2.55/1.00      ( $false ),
% 2.55/1.00      inference(minisat,[status(thm)],[c_3032,c_25,c_24]) ).
% 2.55/1.00  
% 2.55/1.00  
% 2.55/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.55/1.00  
% 2.55/1.00  ------                               Statistics
% 2.55/1.00  
% 2.55/1.00  ------ General
% 2.55/1.00  
% 2.55/1.00  abstr_ref_over_cycles:                  0
% 2.55/1.00  abstr_ref_under_cycles:                 0
% 2.55/1.00  gc_basic_clause_elim:                   0
% 2.55/1.00  forced_gc_time:                         0
% 2.55/1.00  parsing_time:                           0.01
% 2.55/1.00  unif_index_cands_time:                  0.
% 2.55/1.00  unif_index_add_time:                    0.
% 2.55/1.00  orderings_time:                         0.
% 2.55/1.00  out_proof_time:                         0.01
% 2.55/1.00  total_time:                             0.13
% 2.55/1.00  num_of_symbols:                         48
% 2.55/1.00  num_of_terms:                           3037
% 2.55/1.00  
% 2.55/1.00  ------ Preprocessing
% 2.55/1.00  
% 2.55/1.00  num_of_splits:                          0
% 2.55/1.00  num_of_split_atoms:                     0
% 2.55/1.00  num_of_reused_defs:                     0
% 2.55/1.00  num_eq_ax_congr_red:                    24
% 2.55/1.00  num_of_sem_filtered_clauses:            1
% 2.55/1.00  num_of_subtypes:                        0
% 2.55/1.00  monotx_restored_types:                  0
% 2.55/1.00  sat_num_of_epr_types:                   0
% 2.55/1.00  sat_num_of_non_cyclic_types:            0
% 2.55/1.00  sat_guarded_non_collapsed_types:        0
% 2.55/1.00  num_pure_diseq_elim:                    0
% 2.55/1.00  simp_replaced_by:                       0
% 2.55/1.00  res_preprocessed:                       121
% 2.55/1.00  prep_upred:                             0
% 2.55/1.00  prep_unflattend:                        8
% 2.55/1.00  smt_new_axioms:                         0
% 2.55/1.00  pred_elim_cands:                        4
% 2.55/1.00  pred_elim:                              0
% 2.55/1.00  pred_elim_cl:                           0
% 2.55/1.00  pred_elim_cycles:                       2
% 2.55/1.00  merged_defs:                            0
% 2.55/1.00  merged_defs_ncl:                        0
% 2.55/1.00  bin_hyper_res:                          0
% 2.55/1.00  prep_cycles:                            4
% 2.55/1.00  pred_elim_time:                         0.003
% 2.55/1.00  splitting_time:                         0.
% 2.55/1.00  sem_filter_time:                        0.
% 2.55/1.00  monotx_time:                            0.001
% 2.55/1.00  subtype_inf_time:                       0.
% 2.55/1.00  
% 2.55/1.00  ------ Problem properties
% 2.55/1.00  
% 2.55/1.00  clauses:                                23
% 2.55/1.00  conjectures:                            3
% 2.55/1.00  epr:                                    3
% 2.55/1.00  horn:                                   20
% 2.55/1.00  ground:                                 3
% 2.55/1.00  unary:                                  6
% 2.55/1.00  binary:                                 9
% 2.55/1.00  lits:                                   61
% 2.55/1.00  lits_eq:                                16
% 2.55/1.00  fd_pure:                                0
% 2.55/1.00  fd_pseudo:                              0
% 2.55/1.00  fd_cond:                                0
% 2.55/1.00  fd_pseudo_cond:                         0
% 2.55/1.00  ac_symbols:                             0
% 2.55/1.00  
% 2.55/1.00  ------ Propositional Solver
% 2.55/1.00  
% 2.55/1.00  prop_solver_calls:                      27
% 2.55/1.00  prop_fast_solver_calls:                 791
% 2.55/1.00  smt_solver_calls:                       0
% 2.55/1.00  smt_fast_solver_calls:                  0
% 2.55/1.00  prop_num_of_clauses:                    1213
% 2.55/1.00  prop_preprocess_simplified:             4578
% 2.55/1.00  prop_fo_subsumed:                       15
% 2.55/1.00  prop_solver_time:                       0.
% 2.55/1.00  smt_solver_time:                        0.
% 2.55/1.00  smt_fast_solver_time:                   0.
% 2.55/1.00  prop_fast_solver_time:                  0.
% 2.55/1.00  prop_unsat_core_time:                   0.
% 2.55/1.00  
% 2.55/1.00  ------ QBF
% 2.55/1.00  
% 2.55/1.00  qbf_q_res:                              0
% 2.55/1.00  qbf_num_tautologies:                    0
% 2.55/1.00  qbf_prep_cycles:                        0
% 2.55/1.00  
% 2.55/1.00  ------ BMC1
% 2.55/1.00  
% 2.55/1.00  bmc1_current_bound:                     -1
% 2.55/1.00  bmc1_last_solved_bound:                 -1
% 2.55/1.00  bmc1_unsat_core_size:                   -1
% 2.55/1.00  bmc1_unsat_core_parents_size:           -1
% 2.55/1.00  bmc1_merge_next_fun:                    0
% 2.55/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.55/1.00  
% 2.55/1.00  ------ Instantiation
% 2.55/1.00  
% 2.55/1.00  inst_num_of_clauses:                    355
% 2.55/1.00  inst_num_in_passive:                    145
% 2.55/1.00  inst_num_in_active:                     183
% 2.55/1.00  inst_num_in_unprocessed:                27
% 2.55/1.00  inst_num_of_loops:                      230
% 2.55/1.00  inst_num_of_learning_restarts:          0
% 2.55/1.00  inst_num_moves_active_passive:          44
% 2.55/1.00  inst_lit_activity:                      0
% 2.55/1.00  inst_lit_activity_moves:                0
% 2.55/1.00  inst_num_tautologies:                   0
% 2.55/1.00  inst_num_prop_implied:                  0
% 2.55/1.00  inst_num_existing_simplified:           0
% 2.55/1.00  inst_num_eq_res_simplified:             0
% 2.55/1.00  inst_num_child_elim:                    0
% 2.55/1.00  inst_num_of_dismatching_blockings:      8
% 2.55/1.00  inst_num_of_non_proper_insts:           215
% 2.55/1.00  inst_num_of_duplicates:                 0
% 2.55/1.00  inst_inst_num_from_inst_to_res:         0
% 2.55/1.00  inst_dismatching_checking_time:         0.
% 2.55/1.00  
% 2.55/1.00  ------ Resolution
% 2.55/1.00  
% 2.55/1.00  res_num_of_clauses:                     0
% 2.55/1.00  res_num_in_passive:                     0
% 2.55/1.00  res_num_in_active:                      0
% 2.55/1.00  res_num_of_loops:                       125
% 2.55/1.00  res_forward_subset_subsumed:            8
% 2.55/1.00  res_backward_subset_subsumed:           0
% 2.55/1.00  res_forward_subsumed:                   0
% 2.55/1.00  res_backward_subsumed:                  0
% 2.55/1.00  res_forward_subsumption_resolution:     0
% 2.55/1.00  res_backward_subsumption_resolution:    0
% 2.55/1.00  res_clause_to_clause_subsumption:       68
% 2.55/1.00  res_orphan_elimination:                 0
% 2.55/1.00  res_tautology_del:                      10
% 2.55/1.00  res_num_eq_res_simplified:              0
% 2.55/1.00  res_num_sel_changes:                    0
% 2.55/1.00  res_moves_from_active_to_pass:          0
% 2.55/1.00  
% 2.55/1.00  ------ Superposition
% 2.55/1.00  
% 2.55/1.00  sup_time_total:                         0.
% 2.55/1.00  sup_time_generating:                    0.
% 2.55/1.00  sup_time_sim_full:                      0.
% 2.55/1.00  sup_time_sim_immed:                     0.
% 2.55/1.00  
% 2.55/1.00  sup_num_of_clauses:                     61
% 2.55/1.00  sup_num_in_active:                      46
% 2.55/1.00  sup_num_in_passive:                     15
% 2.55/1.00  sup_num_of_loops:                       45
% 2.55/1.00  sup_fw_superposition:                   30
% 2.55/1.00  sup_bw_superposition:                   30
% 2.55/1.00  sup_immediate_simplified:               18
% 2.55/1.00  sup_given_eliminated:                   0
% 2.55/1.00  comparisons_done:                       0
% 2.55/1.00  comparisons_avoided:                    0
% 2.55/1.00  
% 2.55/1.00  ------ Simplifications
% 2.55/1.00  
% 2.55/1.00  
% 2.55/1.00  sim_fw_subset_subsumed:                 1
% 2.55/1.00  sim_bw_subset_subsumed:                 0
% 2.55/1.00  sim_fw_subsumed:                        1
% 2.55/1.00  sim_bw_subsumed:                        1
% 2.55/1.00  sim_fw_subsumption_res:                 2
% 2.55/1.00  sim_bw_subsumption_res:                 0
% 2.55/1.00  sim_tautology_del:                      0
% 2.55/1.00  sim_eq_tautology_del:                   4
% 2.55/1.00  sim_eq_res_simp:                        0
% 2.55/1.00  sim_fw_demodulated:                     1
% 2.55/1.00  sim_bw_demodulated:                     0
% 2.55/1.00  sim_light_normalised:                   14
% 2.55/1.00  sim_joinable_taut:                      0
% 2.55/1.00  sim_joinable_simp:                      0
% 2.55/1.00  sim_ac_normalised:                      0
% 2.55/1.00  sim_smt_subsumption:                    0
% 2.55/1.00  
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 11:44:56 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 368 expanded)
%              Number of clauses        :   51 ( 126 expanded)
%              Number of leaves         :   12 (  70 expanded)
%              Depth                    :   23
%              Number of atoms          :  274 (1299 expanded)
%              Number of equality atoms :  138 ( 429 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f19])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
        | k1_xboole_0 != k7_relat_1(sK3,sK2) )
      & ( r1_xboole_0(k1_relat_1(sK3),sK2)
        | k1_xboole_0 = k7_relat_1(sK3,sK2) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
      | k1_xboole_0 != k7_relat_1(sK3,sK2) )
    & ( r1_xboole_0(k1_relat_1(sK3),sK2)
      | k1_xboole_0 = k7_relat_1(sK3,sK2) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f29])).

fof(f48,plain,
    ( r1_xboole_0(k1_relat_1(sK3),sK2)
    | k1_xboole_0 = k7_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f21])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f23])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f49,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
    | k1_xboole_0 != k7_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1091,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1092,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1088,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_17,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK3),sK2)
    | k1_xboole_0 = k7_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1081,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,sK2)
    | r1_xboole_0(k1_relat_1(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1090,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_14,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1084,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2))) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1333,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = k1_xboole_0
    | r2_hidden(sK1(k1_relat_1(k7_relat_1(X0,X1))),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_1084])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1083,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1332,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = k1_xboole_0
    | r2_hidden(sK1(k1_relat_1(k7_relat_1(X0,X1))),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_1083])).

cnf(c_0,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1093,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1591,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = k1_xboole_0
    | r2_hidden(sK1(k1_relat_1(k7_relat_1(X0,X1))),X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1332,c_1093])).

cnf(c_2051,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1333,c_1591])).

cnf(c_2456,plain,
    ( k7_relat_1(sK3,sK2) = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,sK2)) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1081,c_2051])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2472,plain,
    ( ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,sK2) = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,sK2)) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2456])).

cnf(c_2477,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = k1_xboole_0
    | k7_relat_1(sK3,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2456,c_18,c_2472])).

cnf(c_2478,plain,
    ( k7_relat_1(sK3,sK2) = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,sK2)) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2477])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1086,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2483,plain,
    ( k7_relat_1(sK3,sK2) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_1086])).

cnf(c_2569,plain,
    ( k7_relat_1(sK3,sK2) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1088,c_2483])).

cnf(c_19,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2764,plain,
    ( k7_relat_1(sK3,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2569,c_19])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1085,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(X2)) != iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2783,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X0,k1_relat_1(k1_xboole_0)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2764,c_1085])).

cnf(c_10,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2812,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2783,c_10])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_7,negated_conjecture,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1089,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1264,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1089])).

cnf(c_2898,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2812,c_19,c_1264])).

cnf(c_2906,plain,
    ( r2_hidden(sK0(X0,k1_relat_1(sK3)),sK2) != iProver_top
    | r1_xboole_0(X0,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1092,c_2898])).

cnf(c_4958,plain,
    ( r1_xboole_0(sK2,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1091,c_2906])).

cnf(c_1363,plain,
    ( r2_hidden(sK0(X0,X1),X2) != iProver_top
    | r1_xboole_0(X2,X0) != iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1091,c_1093])).

cnf(c_1484,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1092,c_1363])).

cnf(c_4998,plain,
    ( r1_xboole_0(k1_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4958,c_1484])).

cnf(c_16,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
    | k1_xboole_0 != k7_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1082,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,sK2)
    | r1_xboole_0(k1_relat_1(sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2768,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK3),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2764,c_1082])).

cnf(c_2769,plain,
    ( r1_xboole_0(k1_relat_1(sK3),sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2768])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4998,c_2769])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 21:08:00 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 3.44/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/0.98  
% 3.44/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.44/0.98  
% 3.44/0.98  ------  iProver source info
% 3.44/0.98  
% 3.44/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.44/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.44/0.98  git: non_committed_changes: false
% 3.44/0.98  git: last_make_outside_of_git: false
% 3.44/0.98  
% 3.44/0.98  ------ 
% 3.44/0.98  ------ Parsing...
% 3.44/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.44/0.98  
% 3.44/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.44/0.98  
% 3.44/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.44/0.98  
% 3.44/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.44/0.98  ------ Proving...
% 3.44/0.98  ------ Problem Properties 
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  clauses                                 19
% 3.44/0.98  conjectures                             5
% 3.44/0.98  EPR                                     2
% 3.44/0.98  Horn                                    14
% 3.44/0.98  unary                                   6
% 3.44/0.98  binary                                  6
% 3.44/0.98  lits                                    40
% 3.44/0.98  lits eq                                 14
% 3.44/0.98  fd_pure                                 0
% 3.44/0.98  fd_pseudo                               0
% 3.44/0.98  fd_cond                                 4
% 3.44/0.98  fd_pseudo_cond                          0
% 3.44/0.98  AC symbols                              0
% 3.44/0.98  
% 3.44/0.98  ------ Input Options Time Limit: Unbounded
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  ------ Preprocessing... sf_s  rm: 15 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.44/0.98  Current options:
% 3.44/0.98  ------ 
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  ------ Proving...
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  ------ Preprocessing... sf_s  rm: 15 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.44/0.98  
% 3.44/0.98  ------ Proving...
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.44/0.98  
% 3.44/0.98  ------ Proving...
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  % SZS status Theorem for theBenchmark.p
% 3.44/0.98  
% 3.44/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.44/0.98  
% 3.44/0.98  fof(f1,axiom,(
% 3.44/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.44/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f11,plain,(
% 3.44/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.44/0.98    inference(rectify,[],[f1])).
% 3.44/0.98  
% 3.44/0.98  fof(f12,plain,(
% 3.44/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.44/0.98    inference(ennf_transformation,[],[f11])).
% 3.44/0.98  
% 3.44/0.98  fof(f19,plain,(
% 3.44/0.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.44/0.98    introduced(choice_axiom,[])).
% 3.44/0.98  
% 3.44/0.98  fof(f20,plain,(
% 3.44/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.44/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f19])).
% 3.44/0.98  
% 3.44/0.98  fof(f31,plain,(
% 3.44/0.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.44/0.98    inference(cnf_transformation,[],[f20])).
% 3.44/0.98  
% 3.44/0.98  fof(f32,plain,(
% 3.44/0.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.44/0.98    inference(cnf_transformation,[],[f20])).
% 3.44/0.98  
% 3.44/0.98  fof(f5,axiom,(
% 3.44/0.98    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.44/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f14,plain,(
% 3.44/0.98    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.44/0.98    inference(ennf_transformation,[],[f5])).
% 3.44/0.98  
% 3.44/0.98  fof(f39,plain,(
% 3.44/0.98    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.44/0.98    inference(cnf_transformation,[],[f14])).
% 3.44/0.98  
% 3.44/0.98  fof(f9,conjecture,(
% 3.44/0.98    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 3.44/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f10,negated_conjecture,(
% 3.44/0.98    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 3.44/0.98    inference(negated_conjecture,[],[f9])).
% 3.44/0.98  
% 3.44/0.98  fof(f18,plain,(
% 3.44/0.98    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 3.44/0.98    inference(ennf_transformation,[],[f10])).
% 3.44/0.98  
% 3.44/0.98  fof(f27,plain,(
% 3.44/0.98    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 3.44/0.98    inference(nnf_transformation,[],[f18])).
% 3.44/0.98  
% 3.44/0.98  fof(f28,plain,(
% 3.44/0.98    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 3.44/0.98    inference(flattening,[],[f27])).
% 3.44/0.98  
% 3.44/0.98  fof(f29,plain,(
% 3.44/0.98    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 != k7_relat_1(sK3,sK2)) & (r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 = k7_relat_1(sK3,sK2)) & v1_relat_1(sK3))),
% 3.44/0.98    introduced(choice_axiom,[])).
% 3.44/0.98  
% 3.44/0.98  fof(f30,plain,(
% 3.44/0.98    (~r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 != k7_relat_1(sK3,sK2)) & (r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 = k7_relat_1(sK3,sK2)) & v1_relat_1(sK3)),
% 3.44/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f29])).
% 3.44/0.98  
% 3.44/0.98  fof(f48,plain,(
% 3.44/0.98    r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 = k7_relat_1(sK3,sK2)),
% 3.44/0.98    inference(cnf_transformation,[],[f30])).
% 3.44/0.98  
% 3.44/0.98  fof(f2,axiom,(
% 3.44/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.44/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f13,plain,(
% 3.44/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.44/0.98    inference(ennf_transformation,[],[f2])).
% 3.44/0.98  
% 3.44/0.98  fof(f21,plain,(
% 3.44/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.44/0.98    introduced(choice_axiom,[])).
% 3.44/0.98  
% 3.44/0.98  fof(f22,plain,(
% 3.44/0.98    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.44/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f21])).
% 3.44/0.98  
% 3.44/0.98  fof(f34,plain,(
% 3.44/0.98    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.44/0.98    inference(cnf_transformation,[],[f22])).
% 3.44/0.98  
% 3.44/0.98  fof(f8,axiom,(
% 3.44/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 3.44/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f17,plain,(
% 3.44/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 3.44/0.98    inference(ennf_transformation,[],[f8])).
% 3.44/0.98  
% 3.44/0.98  fof(f25,plain,(
% 3.44/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 3.44/0.98    inference(nnf_transformation,[],[f17])).
% 3.44/0.98  
% 3.44/0.98  fof(f26,plain,(
% 3.44/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 3.44/0.98    inference(flattening,[],[f25])).
% 3.44/0.98  
% 3.44/0.98  fof(f45,plain,(
% 3.44/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 3.44/0.98    inference(cnf_transformation,[],[f26])).
% 3.44/0.98  
% 3.44/0.98  fof(f44,plain,(
% 3.44/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 3.44/0.98    inference(cnf_transformation,[],[f26])).
% 3.44/0.98  
% 3.44/0.98  fof(f33,plain,(
% 3.44/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.44/0.98    inference(cnf_transformation,[],[f20])).
% 3.44/0.98  
% 3.44/0.98  fof(f47,plain,(
% 3.44/0.98    v1_relat_1(sK3)),
% 3.44/0.98    inference(cnf_transformation,[],[f30])).
% 3.44/0.98  
% 3.44/0.98  fof(f7,axiom,(
% 3.44/0.98    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.44/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f15,plain,(
% 3.44/0.98    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.44/0.98    inference(ennf_transformation,[],[f7])).
% 3.44/0.98  
% 3.44/0.98  fof(f16,plain,(
% 3.44/0.98    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.44/0.98    inference(flattening,[],[f15])).
% 3.44/0.98  
% 3.44/0.98  fof(f42,plain,(
% 3.44/0.98    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.44/0.98    inference(cnf_transformation,[],[f16])).
% 3.44/0.98  
% 3.44/0.98  fof(f46,plain,(
% 3.44/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 3.44/0.98    inference(cnf_transformation,[],[f26])).
% 3.44/0.98  
% 3.44/0.98  fof(f6,axiom,(
% 3.44/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.44/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f40,plain,(
% 3.44/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.44/0.98    inference(cnf_transformation,[],[f6])).
% 3.44/0.98  
% 3.44/0.98  fof(f3,axiom,(
% 3.44/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.44/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f23,plain,(
% 3.44/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.44/0.98    inference(nnf_transformation,[],[f3])).
% 3.44/0.98  
% 3.44/0.98  fof(f24,plain,(
% 3.44/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.44/0.98    inference(flattening,[],[f23])).
% 3.44/0.98  
% 3.44/0.98  fof(f37,plain,(
% 3.44/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.44/0.98    inference(cnf_transformation,[],[f24])).
% 3.44/0.98  
% 3.44/0.98  fof(f50,plain,(
% 3.44/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.44/0.98    inference(equality_resolution,[],[f37])).
% 3.44/0.98  
% 3.44/0.98  fof(f4,axiom,(
% 3.44/0.98    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 3.44/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f38,plain,(
% 3.44/0.98    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 3.44/0.98    inference(cnf_transformation,[],[f4])).
% 3.44/0.98  
% 3.44/0.98  fof(f49,plain,(
% 3.44/0.98    ~r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 != k7_relat_1(sK3,sK2)),
% 3.44/0.98    inference(cnf_transformation,[],[f30])).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2,plain,
% 3.44/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.44/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1091,plain,
% 3.44/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.44/0.98      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1,plain,
% 3.44/0.98      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.44/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1092,plain,
% 3.44/0.98      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.44/0.98      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_8,plain,
% 3.44/0.98      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.44/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1088,plain,
% 3.44/0.98      ( v1_relat_1(X0) != iProver_top
% 3.44/0.98      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_17,negated_conjecture,
% 3.44/0.98      ( r1_xboole_0(k1_relat_1(sK3),sK2)
% 3.44/0.98      | k1_xboole_0 = k7_relat_1(sK3,sK2) ),
% 3.44/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1081,plain,
% 3.44/0.98      ( k1_xboole_0 = k7_relat_1(sK3,sK2)
% 3.44/0.98      | r1_xboole_0(k1_relat_1(sK3),sK2) = iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_3,plain,
% 3.44/0.98      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.44/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1090,plain,
% 3.44/0.98      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_14,plain,
% 3.44/0.98      ( r2_hidden(X0,k1_relat_1(X1))
% 3.44/0.98      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
% 3.44/0.98      | ~ v1_relat_1(X1) ),
% 3.44/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1084,plain,
% 3.44/0.98      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 3.44/0.98      | r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2))) != iProver_top
% 3.44/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1333,plain,
% 3.44/0.98      ( k1_relat_1(k7_relat_1(X0,X1)) = k1_xboole_0
% 3.44/0.98      | r2_hidden(sK1(k1_relat_1(k7_relat_1(X0,X1))),k1_relat_1(X0)) = iProver_top
% 3.44/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1090,c_1084]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_15,plain,
% 3.44/0.98      ( r2_hidden(X0,X1)
% 3.44/0.98      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 3.44/0.98      | ~ v1_relat_1(X2) ),
% 3.44/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1083,plain,
% 3.44/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.44/0.98      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
% 3.44/0.98      | v1_relat_1(X2) != iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1332,plain,
% 3.44/0.98      ( k1_relat_1(k7_relat_1(X0,X1)) = k1_xboole_0
% 3.44/0.98      | r2_hidden(sK1(k1_relat_1(k7_relat_1(X0,X1))),X1) = iProver_top
% 3.44/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1090,c_1083]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_0,negated_conjecture,
% 3.44/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.44/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1093,plain,
% 3.44/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.44/0.98      | r2_hidden(X0,X2) != iProver_top
% 3.44/0.98      | r1_xboole_0(X2,X1) != iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1591,plain,
% 3.44/0.98      ( k1_relat_1(k7_relat_1(X0,X1)) = k1_xboole_0
% 3.44/0.98      | r2_hidden(sK1(k1_relat_1(k7_relat_1(X0,X1))),X2) != iProver_top
% 3.44/0.98      | r1_xboole_0(X2,X1) != iProver_top
% 3.44/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1332,c_1093]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2051,plain,
% 3.44/0.98      ( k1_relat_1(k7_relat_1(X0,X1)) = k1_xboole_0
% 3.44/0.98      | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
% 3.44/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1333,c_1591]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2456,plain,
% 3.44/0.98      ( k7_relat_1(sK3,sK2) = k1_xboole_0
% 3.44/0.98      | k1_relat_1(k7_relat_1(sK3,sK2)) = k1_xboole_0
% 3.44/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1081,c_2051]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_18,negated_conjecture,
% 3.44/0.98      ( v1_relat_1(sK3) ),
% 3.44/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2472,plain,
% 3.44/0.98      ( ~ v1_relat_1(sK3)
% 3.44/0.98      | k7_relat_1(sK3,sK2) = k1_xboole_0
% 3.44/0.98      | k1_relat_1(k7_relat_1(sK3,sK2)) = k1_xboole_0 ),
% 3.44/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2456]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2477,plain,
% 3.44/0.98      ( k1_relat_1(k7_relat_1(sK3,sK2)) = k1_xboole_0
% 3.44/0.98      | k7_relat_1(sK3,sK2) = k1_xboole_0 ),
% 3.44/0.98      inference(global_propositional_subsumption,
% 3.44/0.98                [status(thm)],
% 3.44/0.98                [c_2456,c_18,c_2472]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2478,plain,
% 3.44/0.98      ( k7_relat_1(sK3,sK2) = k1_xboole_0
% 3.44/0.98      | k1_relat_1(k7_relat_1(sK3,sK2)) = k1_xboole_0 ),
% 3.44/0.98      inference(renaming,[status(thm)],[c_2477]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_12,plain,
% 3.44/0.98      ( ~ v1_relat_1(X0)
% 3.44/0.98      | k1_relat_1(X0) != k1_xboole_0
% 3.44/0.98      | k1_xboole_0 = X0 ),
% 3.44/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1086,plain,
% 3.44/0.98      ( k1_relat_1(X0) != k1_xboole_0
% 3.44/0.98      | k1_xboole_0 = X0
% 3.44/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2483,plain,
% 3.44/0.98      ( k7_relat_1(sK3,sK2) = k1_xboole_0
% 3.44/0.98      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_2478,c_1086]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2569,plain,
% 3.44/0.98      ( k7_relat_1(sK3,sK2) = k1_xboole_0
% 3.44/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1088,c_2483]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_19,plain,
% 3.44/0.98      ( v1_relat_1(sK3) = iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2764,plain,
% 3.44/0.98      ( k7_relat_1(sK3,sK2) = k1_xboole_0 ),
% 3.44/0.98      inference(global_propositional_subsumption,
% 3.44/0.98                [status(thm)],
% 3.44/0.98                [c_2569,c_19]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_13,plain,
% 3.44/0.98      ( ~ r2_hidden(X0,X1)
% 3.44/0.98      | ~ r2_hidden(X0,k1_relat_1(X2))
% 3.44/0.98      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 3.44/0.98      | ~ v1_relat_1(X2) ),
% 3.44/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1085,plain,
% 3.44/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.44/0.98      | r2_hidden(X0,k1_relat_1(X2)) != iProver_top
% 3.44/0.98      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) = iProver_top
% 3.44/0.98      | v1_relat_1(X2) != iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2783,plain,
% 3.44/0.98      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 3.44/0.98      | r2_hidden(X0,k1_relat_1(k1_xboole_0)) = iProver_top
% 3.44/0.98      | r2_hidden(X0,sK2) != iProver_top
% 3.44/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_2764,c_1085]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_10,plain,
% 3.44/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.44/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2812,plain,
% 3.44/0.98      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 3.44/0.98      | r2_hidden(X0,sK2) != iProver_top
% 3.44/0.98      | r2_hidden(X0,k1_xboole_0) = iProver_top
% 3.44/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.44/0.98      inference(light_normalisation,[status(thm)],[c_2783,c_10]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_4,plain,
% 3.44/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.44/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_7,negated_conjecture,
% 3.44/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 3.44/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1089,plain,
% 3.44/0.98      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1264,plain,
% 3.44/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_4,c_1089]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2898,plain,
% 3.44/0.98      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 3.44/0.98      | r2_hidden(X0,sK2) != iProver_top ),
% 3.44/0.98      inference(global_propositional_subsumption,
% 3.44/0.98                [status(thm)],
% 3.44/0.98                [c_2812,c_19,c_1264]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2906,plain,
% 3.44/0.98      ( r2_hidden(sK0(X0,k1_relat_1(sK3)),sK2) != iProver_top
% 3.44/0.98      | r1_xboole_0(X0,k1_relat_1(sK3)) = iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1092,c_2898]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_4958,plain,
% 3.44/0.98      ( r1_xboole_0(sK2,k1_relat_1(sK3)) = iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1091,c_2906]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1363,plain,
% 3.44/0.98      ( r2_hidden(sK0(X0,X1),X2) != iProver_top
% 3.44/0.98      | r1_xboole_0(X2,X0) != iProver_top
% 3.44/0.98      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1091,c_1093]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1484,plain,
% 3.44/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 3.44/0.98      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1092,c_1363]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_4998,plain,
% 3.44/0.98      ( r1_xboole_0(k1_relat_1(sK3),sK2) = iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_4958,c_1484]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_16,negated_conjecture,
% 3.44/0.98      ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
% 3.44/0.98      | k1_xboole_0 != k7_relat_1(sK3,sK2) ),
% 3.44/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1082,plain,
% 3.44/0.98      ( k1_xboole_0 != k7_relat_1(sK3,sK2)
% 3.44/0.98      | r1_xboole_0(k1_relat_1(sK3),sK2) != iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2768,plain,
% 3.44/0.98      ( k1_xboole_0 != k1_xboole_0
% 3.44/0.98      | r1_xboole_0(k1_relat_1(sK3),sK2) != iProver_top ),
% 3.44/0.98      inference(demodulation,[status(thm)],[c_2764,c_1082]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2769,plain,
% 3.44/0.98      ( r1_xboole_0(k1_relat_1(sK3),sK2) != iProver_top ),
% 3.44/0.98      inference(equality_resolution_simp,[status(thm)],[c_2768]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(contradiction,plain,
% 3.44/0.98      ( $false ),
% 3.44/0.98      inference(minisat,[status(thm)],[c_4998,c_2769]) ).
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.44/0.98  
% 3.44/0.98  ------                               Statistics
% 3.44/0.98  
% 3.44/0.98  ------ Selected
% 3.44/0.98  
% 3.44/0.98  total_time:                             0.136
% 3.44/0.98  
%------------------------------------------------------------------------------

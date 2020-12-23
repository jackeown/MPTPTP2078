%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:30 EST 2020

% Result     : CounterSatisfiable 2.03s
% Output     : Saturation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  130 (2070 expanded)
%              Number of clauses        :   85 ( 707 expanded)
%              Number of leaves         :   13 ( 403 expanded)
%              Depth                    :   17
%              Number of atoms          :  366 (7751 expanded)
%              Number of equality atoms :  175 (1531 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
      | r1_tarski(sK1(X0,X1),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(rectify,[],[f2])).

fof(f15,plain,(
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

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f23])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ r2_hidden(X2,X1) )
              & k1_struct_0(X0) != X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r2_hidden(X2,X1) )
                & k1_struct_0(X0) != X1 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f13,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => ~ ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ r2_hidden(X2,X1) )
            & k1_struct_0(X0) != X1 ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      & k1_struct_0(X0) != X1
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      & k1_struct_0(X0) != X1
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(flattening,[],[f21])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & k1_struct_0(X0) != X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
   => ( ! [X2] :
          ( ~ r2_hidden(X2,sK3)
          | ~ m1_subset_1(X2,u1_struct_0(sK2)) )
      & k1_struct_0(sK2) != sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK2)) )
    & k1_struct_0(sK2) != sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f22,f29])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK3)
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    k1_struct_0(sK2) != sK3 ),
    inference(cnf_transformation,[],[f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
      | ~ r1_tarski(sK1(X0,X1),X0)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_185,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_701,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_6,plain,
    ( r1_tarski(sK1(X0,X1),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k1_zfmisc_1(X0) = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1050,plain,
    ( k1_zfmisc_1(X0) = X1
    | r1_tarski(sK1(X0,X1),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1048,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1557,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | r1_tarski(sK1(X1,k1_zfmisc_1(X0)),X1) = iProver_top
    | r1_tarski(sK1(X1,k1_zfmisc_1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1050,c_1048])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1049,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1055,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2003,plain,
    ( k1_zfmisc_1(X0) = X1
    | r1_tarski(sK1(X0,X1),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1050,c_1055])).

cnf(c_3161,plain,
    ( k1_zfmisc_1(X0) = X1
    | r1_tarski(sK1(X0,X1),X2) != iProver_top
    | r1_tarski(sK1(X0,X1),X0) = iProver_top
    | r1_xboole_0(k1_zfmisc_1(X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1049,c_2003])).

cnf(c_3282,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | r1_tarski(sK1(X0,k1_zfmisc_1(X1)),X0) = iProver_top
    | r1_tarski(sK1(X0,k1_zfmisc_1(X1)),X1) = iProver_top
    | r1_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_3161])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1052,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3402,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | r1_tarski(sK1(X1,k1_zfmisc_1(X0)),X0) = iProver_top
    | r1_xboole_0(sK1(X1,k1_zfmisc_1(X0)),X1) != iProver_top
    | r1_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(sK1(X1,k1_zfmisc_1(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3282,c_1052])).

cnf(c_3399,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | r1_tarski(sK1(X1,k1_zfmisc_1(X0)),X1) = iProver_top
    | r1_xboole_0(sK1(X1,k1_zfmisc_1(X0)),X0) != iProver_top
    | r1_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(sK1(X1,k1_zfmisc_1(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3282,c_1052])).

cnf(c_3160,plain,
    ( k1_zfmisc_1(X0) = X1
    | r1_tarski(sK1(X0,X1),X0) = iProver_top
    | r1_xboole_0(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1050,c_2003])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1053,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2002,plain,
    ( r2_hidden(sK0(X0,X1),X2) != iProver_top
    | r1_xboole_0(X2,X0) != iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_1055])).

cnf(c_2770,plain,
    ( r1_tarski(sK0(X0,X1),X2) != iProver_top
    | r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(k1_zfmisc_1(X2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1049,c_2002])).

cnf(c_2769,plain,
    ( r1_xboole_0(X0,X0) != iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_2002])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1054,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2768,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1054,c_2002])).

cnf(c_2001,plain,
    ( r2_hidden(sK0(X0,X1),X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1054,c_1055])).

cnf(c_2570,plain,
    ( r1_tarski(sK0(X0,X1),X2) != iProver_top
    | r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(k1_zfmisc_1(X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1049,c_2001])).

cnf(c_2568,plain,
    ( r1_xboole_0(X0,X0) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1054,c_2001])).

cnf(c_2508,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | r1_tarski(sK1(X0,k1_zfmisc_1(X1)),X1) = iProver_top
    | r1_xboole_0(sK1(X0,k1_zfmisc_1(X1)),X0) != iProver_top
    | v1_xboole_0(sK1(X0,k1_zfmisc_1(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_1052])).

cnf(c_2506,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | r1_tarski(sK1(X0,k1_zfmisc_1(X1)),X0) = iProver_top
    | r1_xboole_0(sK1(X0,k1_zfmisc_1(X1)),X1) != iProver_top
    | v1_xboole_0(sK1(X0,k1_zfmisc_1(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_1052])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_215,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(u1_struct_0(sK2)) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_216,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_215])).

cnf(c_9,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_222,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_216,c_9])).

cnf(c_1045,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_1317,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_1048])).

cnf(c_1488,plain,
    ( r1_xboole_0(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_1052])).

cnf(c_224,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_1144,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1145,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1144])).

cnf(c_1170,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK2))
    | ~ r1_xboole_0(sK3,u1_struct_0(sK2))
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1177,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top
    | r1_xboole_0(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1170])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_12,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_203,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,sK3)
    | X2 != X0
    | u1_struct_0(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_12])).

cnf(c_204,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_1046,plain,
    ( r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_204])).

cnf(c_1469,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(sK2)),sK3) != iProver_top
    | r1_xboole_0(X0,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1054,c_1046])).

cnf(c_1667,plain,
    ( r1_xboole_0(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_1469])).

cnf(c_1785,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1488,c_224,c_1145,c_1177,c_1667])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1056,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1790,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1785,c_1056])).

cnf(c_1799,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1790,c_1045])).

cnf(c_2203,plain,
    ( r2_hidden(k1_xboole_0,X0) != iProver_top
    | r1_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1799,c_1055])).

cnf(c_1468,plain,
    ( r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1) = iProver_top
    | r1_xboole_0(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1054,c_1048])).

cnf(c_2131,plain,
    ( r1_xboole_0(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_xboole_0(sK0(X0,k1_zfmisc_1(X1)),X1) != iProver_top
    | v1_xboole_0(sK0(X0,k1_zfmisc_1(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1052])).

cnf(c_1386,plain,
    ( r1_tarski(sK0(k1_zfmisc_1(X0),X1),X0) = iProver_top
    | r1_xboole_0(k1_zfmisc_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_1048])).

cnf(c_2042,plain,
    ( r1_xboole_0(sK0(k1_zfmisc_1(X0),X1),X0) != iProver_top
    | r1_xboole_0(k1_zfmisc_1(X0),X1) = iProver_top
    | v1_xboole_0(sK0(k1_zfmisc_1(X0),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1386,c_1052])).

cnf(c_2004,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1049,c_1055])).

cnf(c_13,negated_conjecture,
    ( k1_struct_0(sK2) != sK3 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1802,plain,
    ( k1_struct_0(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1790,c_13])).

cnf(c_225,plain,
    ( ~ r2_hidden(X0,sK3)
    | k1_zfmisc_1(u1_struct_0(sK2)) != u1_struct_0(sK2)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_226,plain,
    ( ~ r2_hidden(sK3,sK3)
    | k1_zfmisc_1(u1_struct_0(sK2)) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_225])).

cnf(c_1044,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) != u1_struct_0(sK2)
    | r2_hidden(sK3,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_1801,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) != u1_struct_0(sK2)
    | r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1790,c_1044])).

cnf(c_1800,plain,
    ( r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1790,c_1046])).

cnf(c_1798,plain,
    ( r1_tarski(k1_xboole_0,u1_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1790,c_1317])).

cnf(c_1387,plain,
    ( r2_hidden(sK0(u1_struct_0(sK2),X0),sK3) != iProver_top
    | r1_xboole_0(u1_struct_0(sK2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_1046])).

cnf(c_1797,plain,
    ( r2_hidden(sK0(u1_struct_0(sK2),X0),k1_xboole_0) != iProver_top
    | r1_xboole_0(u1_struct_0(sK2),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1790,c_1387])).

cnf(c_1796,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(sK2)),k1_xboole_0) != iProver_top
    | r1_xboole_0(X0,u1_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1790,c_1469])).

cnf(c_1558,plain,
    ( k1_zfmisc_1(X0) = u1_struct_0(sK2)
    | r1_tarski(sK1(X0,u1_struct_0(sK2)),X0) = iProver_top
    | r2_hidden(sK1(X0,u1_struct_0(sK2)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1050,c_1046])).

cnf(c_1795,plain,
    ( k1_zfmisc_1(X0) = u1_struct_0(sK2)
    | r1_tarski(sK1(X0,u1_struct_0(sK2)),X0) = iProver_top
    | r2_hidden(sK1(X0,u1_struct_0(sK2)),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1790,c_1558])).

cnf(c_1590,plain,
    ( r1_xboole_0(u1_struct_0(sK2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1054,c_1387])).

cnf(c_1794,plain,
    ( r1_xboole_0(u1_struct_0(sK2),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1790,c_1590])).

cnf(c_1793,plain,
    ( r1_xboole_0(k1_xboole_0,u1_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1790,c_1667])).

cnf(c_1792,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1790,c_1785])).

cnf(c_1559,plain,
    ( k1_zfmisc_1(X0) = X1
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | r1_xboole_0(sK1(X0,X1),X0) != iProver_top
    | v1_xboole_0(sK1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1050,c_1052])).

cnf(c_5,plain,
    ( ~ r1_tarski(sK1(X0,X1),X0)
    | ~ r2_hidden(sK1(X0,X1),X1)
    | k1_zfmisc_1(X0) = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1051,plain,
    ( k1_zfmisc_1(X0) = X1
    | r1_tarski(sK1(X0,X1),X0) != iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1047,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:03:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.03/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/0.99  
% 2.03/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.03/0.99  
% 2.03/0.99  ------  iProver source info
% 2.03/0.99  
% 2.03/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.03/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.03/0.99  git: non_committed_changes: false
% 2.03/0.99  git: last_make_outside_of_git: false
% 2.03/0.99  
% 2.03/0.99  ------ 
% 2.03/0.99  
% 2.03/0.99  ------ Input Options
% 2.03/0.99  
% 2.03/0.99  --out_options                           all
% 2.03/0.99  --tptp_safe_out                         true
% 2.03/0.99  --problem_path                          ""
% 2.03/0.99  --include_path                          ""
% 2.03/0.99  --clausifier                            res/vclausify_rel
% 2.03/0.99  --clausifier_options                    --mode clausify
% 2.03/0.99  --stdin                                 false
% 2.03/0.99  --stats_out                             all
% 2.03/0.99  
% 2.03/0.99  ------ General Options
% 2.03/0.99  
% 2.03/0.99  --fof                                   false
% 2.03/0.99  --time_out_real                         305.
% 2.03/0.99  --time_out_virtual                      -1.
% 2.03/0.99  --symbol_type_check                     false
% 2.03/0.99  --clausify_out                          false
% 2.03/0.99  --sig_cnt_out                           false
% 2.03/0.99  --trig_cnt_out                          false
% 2.03/0.99  --trig_cnt_out_tolerance                1.
% 2.03/0.99  --trig_cnt_out_sk_spl                   false
% 2.03/0.99  --abstr_cl_out                          false
% 2.03/0.99  
% 2.03/0.99  ------ Global Options
% 2.03/0.99  
% 2.03/0.99  --schedule                              default
% 2.03/0.99  --add_important_lit                     false
% 2.03/0.99  --prop_solver_per_cl                    1000
% 2.03/0.99  --min_unsat_core                        false
% 2.03/0.99  --soft_assumptions                      false
% 2.03/0.99  --soft_lemma_size                       3
% 2.03/0.99  --prop_impl_unit_size                   0
% 2.03/0.99  --prop_impl_unit                        []
% 2.03/0.99  --share_sel_clauses                     true
% 2.03/0.99  --reset_solvers                         false
% 2.03/0.99  --bc_imp_inh                            [conj_cone]
% 2.03/0.99  --conj_cone_tolerance                   3.
% 2.03/0.99  --extra_neg_conj                        none
% 2.03/0.99  --large_theory_mode                     true
% 2.03/0.99  --prolific_symb_bound                   200
% 2.03/0.99  --lt_threshold                          2000
% 2.03/0.99  --clause_weak_htbl                      true
% 2.03/0.99  --gc_record_bc_elim                     false
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing Options
% 2.03/0.99  
% 2.03/0.99  --preprocessing_flag                    true
% 2.03/0.99  --time_out_prep_mult                    0.1
% 2.03/0.99  --splitting_mode                        input
% 2.03/0.99  --splitting_grd                         true
% 2.03/0.99  --splitting_cvd                         false
% 2.03/0.99  --splitting_cvd_svl                     false
% 2.03/0.99  --splitting_nvd                         32
% 2.03/0.99  --sub_typing                            true
% 2.03/0.99  --prep_gs_sim                           true
% 2.03/0.99  --prep_unflatten                        true
% 2.03/0.99  --prep_res_sim                          true
% 2.03/0.99  --prep_upred                            true
% 2.03/0.99  --prep_sem_filter                       exhaustive
% 2.03/0.99  --prep_sem_filter_out                   false
% 2.03/0.99  --pred_elim                             true
% 2.03/0.99  --res_sim_input                         true
% 2.03/0.99  --eq_ax_congr_red                       true
% 2.03/0.99  --pure_diseq_elim                       true
% 2.03/0.99  --brand_transform                       false
% 2.03/0.99  --non_eq_to_eq                          false
% 2.03/0.99  --prep_def_merge                        true
% 2.03/0.99  --prep_def_merge_prop_impl              false
% 2.03/0.99  --prep_def_merge_mbd                    true
% 2.03/0.99  --prep_def_merge_tr_red                 false
% 2.03/0.99  --prep_def_merge_tr_cl                  false
% 2.03/0.99  --smt_preprocessing                     true
% 2.03/0.99  --smt_ac_axioms                         fast
% 2.03/0.99  --preprocessed_out                      false
% 2.03/0.99  --preprocessed_stats                    false
% 2.03/0.99  
% 2.03/0.99  ------ Abstraction refinement Options
% 2.03/0.99  
% 2.03/0.99  --abstr_ref                             []
% 2.03/0.99  --abstr_ref_prep                        false
% 2.03/0.99  --abstr_ref_until_sat                   false
% 2.03/0.99  --abstr_ref_sig_restrict                funpre
% 2.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.03/0.99  --abstr_ref_under                       []
% 2.03/0.99  
% 2.03/0.99  ------ SAT Options
% 2.03/0.99  
% 2.03/0.99  --sat_mode                              false
% 2.03/0.99  --sat_fm_restart_options                ""
% 2.03/0.99  --sat_gr_def                            false
% 2.03/0.99  --sat_epr_types                         true
% 2.03/0.99  --sat_non_cyclic_types                  false
% 2.03/0.99  --sat_finite_models                     false
% 2.03/0.99  --sat_fm_lemmas                         false
% 2.03/0.99  --sat_fm_prep                           false
% 2.03/0.99  --sat_fm_uc_incr                        true
% 2.03/0.99  --sat_out_model                         small
% 2.03/0.99  --sat_out_clauses                       false
% 2.03/0.99  
% 2.03/0.99  ------ QBF Options
% 2.03/0.99  
% 2.03/0.99  --qbf_mode                              false
% 2.03/0.99  --qbf_elim_univ                         false
% 2.03/0.99  --qbf_dom_inst                          none
% 2.03/0.99  --qbf_dom_pre_inst                      false
% 2.03/0.99  --qbf_sk_in                             false
% 2.03/0.99  --qbf_pred_elim                         true
% 2.03/0.99  --qbf_split                             512
% 2.03/0.99  
% 2.03/0.99  ------ BMC1 Options
% 2.03/0.99  
% 2.03/0.99  --bmc1_incremental                      false
% 2.03/0.99  --bmc1_axioms                           reachable_all
% 2.03/0.99  --bmc1_min_bound                        0
% 2.03/0.99  --bmc1_max_bound                        -1
% 2.03/0.99  --bmc1_max_bound_default                -1
% 2.03/0.99  --bmc1_symbol_reachability              true
% 2.03/0.99  --bmc1_property_lemmas                  false
% 2.03/0.99  --bmc1_k_induction                      false
% 2.03/0.99  --bmc1_non_equiv_states                 false
% 2.03/0.99  --bmc1_deadlock                         false
% 2.03/0.99  --bmc1_ucm                              false
% 2.03/0.99  --bmc1_add_unsat_core                   none
% 2.03/0.99  --bmc1_unsat_core_children              false
% 2.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.03/0.99  --bmc1_out_stat                         full
% 2.03/0.99  --bmc1_ground_init                      false
% 2.03/0.99  --bmc1_pre_inst_next_state              false
% 2.03/0.99  --bmc1_pre_inst_state                   false
% 2.03/0.99  --bmc1_pre_inst_reach_state             false
% 2.03/0.99  --bmc1_out_unsat_core                   false
% 2.03/0.99  --bmc1_aig_witness_out                  false
% 2.03/0.99  --bmc1_verbose                          false
% 2.03/0.99  --bmc1_dump_clauses_tptp                false
% 2.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.03/0.99  --bmc1_dump_file                        -
% 2.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.03/0.99  --bmc1_ucm_extend_mode                  1
% 2.03/0.99  --bmc1_ucm_init_mode                    2
% 2.03/0.99  --bmc1_ucm_cone_mode                    none
% 2.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.03/0.99  --bmc1_ucm_relax_model                  4
% 2.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.03/0.99  --bmc1_ucm_layered_model                none
% 2.03/0.99  --bmc1_ucm_max_lemma_size               10
% 2.03/0.99  
% 2.03/0.99  ------ AIG Options
% 2.03/0.99  
% 2.03/0.99  --aig_mode                              false
% 2.03/0.99  
% 2.03/0.99  ------ Instantiation Options
% 2.03/0.99  
% 2.03/0.99  --instantiation_flag                    true
% 2.03/0.99  --inst_sos_flag                         false
% 2.03/0.99  --inst_sos_phase                        true
% 2.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel_side                     num_symb
% 2.03/0.99  --inst_solver_per_active                1400
% 2.03/0.99  --inst_solver_calls_frac                1.
% 2.03/0.99  --inst_passive_queue_type               priority_queues
% 2.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.03/0.99  --inst_passive_queues_freq              [25;2]
% 2.03/0.99  --inst_dismatching                      true
% 2.03/0.99  --inst_eager_unprocessed_to_passive     true
% 2.03/0.99  --inst_prop_sim_given                   true
% 2.03/0.99  --inst_prop_sim_new                     false
% 2.03/0.99  --inst_subs_new                         false
% 2.03/0.99  --inst_eq_res_simp                      false
% 2.03/0.99  --inst_subs_given                       false
% 2.03/0.99  --inst_orphan_elimination               true
% 2.03/0.99  --inst_learning_loop_flag               true
% 2.03/0.99  --inst_learning_start                   3000
% 2.03/0.99  --inst_learning_factor                  2
% 2.03/0.99  --inst_start_prop_sim_after_learn       3
% 2.03/0.99  --inst_sel_renew                        solver
% 2.03/0.99  --inst_lit_activity_flag                true
% 2.03/0.99  --inst_restr_to_given                   false
% 2.03/0.99  --inst_activity_threshold               500
% 2.03/0.99  --inst_out_proof                        true
% 2.03/0.99  
% 2.03/0.99  ------ Resolution Options
% 2.03/0.99  
% 2.03/0.99  --resolution_flag                       true
% 2.03/0.99  --res_lit_sel                           adaptive
% 2.03/0.99  --res_lit_sel_side                      none
% 2.03/0.99  --res_ordering                          kbo
% 2.03/0.99  --res_to_prop_solver                    active
% 2.03/0.99  --res_prop_simpl_new                    false
% 2.03/0.99  --res_prop_simpl_given                  true
% 2.03/0.99  --res_passive_queue_type                priority_queues
% 2.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.03/0.99  --res_passive_queues_freq               [15;5]
% 2.03/0.99  --res_forward_subs                      full
% 2.03/0.99  --res_backward_subs                     full
% 2.03/0.99  --res_forward_subs_resolution           true
% 2.03/0.99  --res_backward_subs_resolution          true
% 2.03/0.99  --res_orphan_elimination                true
% 2.03/0.99  --res_time_limit                        2.
% 2.03/0.99  --res_out_proof                         true
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Options
% 2.03/0.99  
% 2.03/0.99  --superposition_flag                    true
% 2.03/0.99  --sup_passive_queue_type                priority_queues
% 2.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.03/0.99  --demod_completeness_check              fast
% 2.03/0.99  --demod_use_ground                      true
% 2.03/0.99  --sup_to_prop_solver                    passive
% 2.03/0.99  --sup_prop_simpl_new                    true
% 2.03/0.99  --sup_prop_simpl_given                  true
% 2.03/0.99  --sup_fun_splitting                     false
% 2.03/0.99  --sup_smt_interval                      50000
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Simplification Setup
% 2.03/0.99  
% 2.03/0.99  --sup_indices_passive                   []
% 2.03/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_full_bw                           [BwDemod]
% 2.03/0.99  --sup_immed_triv                        [TrivRules]
% 2.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_immed_bw_main                     []
% 2.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  
% 2.03/0.99  ------ Combination Options
% 2.03/0.99  
% 2.03/0.99  --comb_res_mult                         3
% 2.03/0.99  --comb_sup_mult                         2
% 2.03/0.99  --comb_inst_mult                        10
% 2.03/0.99  
% 2.03/0.99  ------ Debug Options
% 2.03/0.99  
% 2.03/0.99  --dbg_backtrace                         false
% 2.03/0.99  --dbg_dump_prop_clauses                 false
% 2.03/0.99  --dbg_dump_prop_clauses_file            -
% 2.03/0.99  --dbg_out_stat                          false
% 2.03/0.99  ------ Parsing...
% 2.03/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.03/0.99  ------ Proving...
% 2.03/0.99  ------ Problem Properties 
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  clauses                                 14
% 2.03/0.99  conjectures                             1
% 2.03/0.99  EPR                                     3
% 2.03/0.99  Horn                                    11
% 2.03/0.99  unary                                   3
% 2.03/0.99  binary                                  7
% 2.03/0.99  lits                                    29
% 2.03/0.99  lits eq                                 5
% 2.03/0.99  fd_pure                                 0
% 2.03/0.99  fd_pseudo                               0
% 2.03/0.99  fd_cond                                 1
% 2.03/0.99  fd_pseudo_cond                          2
% 2.03/0.99  AC symbols                              0
% 2.03/0.99  
% 2.03/0.99  ------ Schedule dynamic 5 is on 
% 2.03/0.99  
% 2.03/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  ------ 
% 2.03/0.99  Current options:
% 2.03/0.99  ------ 
% 2.03/0.99  
% 2.03/0.99  ------ Input Options
% 2.03/0.99  
% 2.03/0.99  --out_options                           all
% 2.03/0.99  --tptp_safe_out                         true
% 2.03/0.99  --problem_path                          ""
% 2.03/0.99  --include_path                          ""
% 2.03/0.99  --clausifier                            res/vclausify_rel
% 2.03/0.99  --clausifier_options                    --mode clausify
% 2.03/0.99  --stdin                                 false
% 2.03/0.99  --stats_out                             all
% 2.03/0.99  
% 2.03/0.99  ------ General Options
% 2.03/0.99  
% 2.03/0.99  --fof                                   false
% 2.03/0.99  --time_out_real                         305.
% 2.03/0.99  --time_out_virtual                      -1.
% 2.03/0.99  --symbol_type_check                     false
% 2.03/0.99  --clausify_out                          false
% 2.03/0.99  --sig_cnt_out                           false
% 2.03/0.99  --trig_cnt_out                          false
% 2.03/0.99  --trig_cnt_out_tolerance                1.
% 2.03/0.99  --trig_cnt_out_sk_spl                   false
% 2.03/0.99  --abstr_cl_out                          false
% 2.03/0.99  
% 2.03/0.99  ------ Global Options
% 2.03/0.99  
% 2.03/0.99  --schedule                              default
% 2.03/0.99  --add_important_lit                     false
% 2.03/0.99  --prop_solver_per_cl                    1000
% 2.03/0.99  --min_unsat_core                        false
% 2.03/0.99  --soft_assumptions                      false
% 2.03/0.99  --soft_lemma_size                       3
% 2.03/0.99  --prop_impl_unit_size                   0
% 2.03/0.99  --prop_impl_unit                        []
% 2.03/0.99  --share_sel_clauses                     true
% 2.03/0.99  --reset_solvers                         false
% 2.03/0.99  --bc_imp_inh                            [conj_cone]
% 2.03/0.99  --conj_cone_tolerance                   3.
% 2.03/0.99  --extra_neg_conj                        none
% 2.03/0.99  --large_theory_mode                     true
% 2.03/0.99  --prolific_symb_bound                   200
% 2.03/0.99  --lt_threshold                          2000
% 2.03/0.99  --clause_weak_htbl                      true
% 2.03/0.99  --gc_record_bc_elim                     false
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing Options
% 2.03/0.99  
% 2.03/0.99  --preprocessing_flag                    true
% 2.03/0.99  --time_out_prep_mult                    0.1
% 2.03/0.99  --splitting_mode                        input
% 2.03/0.99  --splitting_grd                         true
% 2.03/0.99  --splitting_cvd                         false
% 2.03/0.99  --splitting_cvd_svl                     false
% 2.03/0.99  --splitting_nvd                         32
% 2.03/0.99  --sub_typing                            true
% 2.03/0.99  --prep_gs_sim                           true
% 2.03/0.99  --prep_unflatten                        true
% 2.03/0.99  --prep_res_sim                          true
% 2.03/0.99  --prep_upred                            true
% 2.03/0.99  --prep_sem_filter                       exhaustive
% 2.03/0.99  --prep_sem_filter_out                   false
% 2.03/0.99  --pred_elim                             true
% 2.03/0.99  --res_sim_input                         true
% 2.03/0.99  --eq_ax_congr_red                       true
% 2.03/0.99  --pure_diseq_elim                       true
% 2.03/0.99  --brand_transform                       false
% 2.03/0.99  --non_eq_to_eq                          false
% 2.03/0.99  --prep_def_merge                        true
% 2.03/0.99  --prep_def_merge_prop_impl              false
% 2.03/0.99  --prep_def_merge_mbd                    true
% 2.03/0.99  --prep_def_merge_tr_red                 false
% 2.03/0.99  --prep_def_merge_tr_cl                  false
% 2.03/0.99  --smt_preprocessing                     true
% 2.03/0.99  --smt_ac_axioms                         fast
% 2.03/0.99  --preprocessed_out                      false
% 2.03/0.99  --preprocessed_stats                    false
% 2.03/0.99  
% 2.03/0.99  ------ Abstraction refinement Options
% 2.03/0.99  
% 2.03/0.99  --abstr_ref                             []
% 2.03/0.99  --abstr_ref_prep                        false
% 2.03/0.99  --abstr_ref_until_sat                   false
% 2.03/0.99  --abstr_ref_sig_restrict                funpre
% 2.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.03/0.99  --abstr_ref_under                       []
% 2.03/0.99  
% 2.03/0.99  ------ SAT Options
% 2.03/0.99  
% 2.03/0.99  --sat_mode                              false
% 2.03/0.99  --sat_fm_restart_options                ""
% 2.03/0.99  --sat_gr_def                            false
% 2.03/0.99  --sat_epr_types                         true
% 2.03/0.99  --sat_non_cyclic_types                  false
% 2.03/0.99  --sat_finite_models                     false
% 2.03/0.99  --sat_fm_lemmas                         false
% 2.03/0.99  --sat_fm_prep                           false
% 2.03/0.99  --sat_fm_uc_incr                        true
% 2.03/0.99  --sat_out_model                         small
% 2.03/0.99  --sat_out_clauses                       false
% 2.03/0.99  
% 2.03/0.99  ------ QBF Options
% 2.03/0.99  
% 2.03/0.99  --qbf_mode                              false
% 2.03/0.99  --qbf_elim_univ                         false
% 2.03/0.99  --qbf_dom_inst                          none
% 2.03/0.99  --qbf_dom_pre_inst                      false
% 2.03/0.99  --qbf_sk_in                             false
% 2.03/0.99  --qbf_pred_elim                         true
% 2.03/0.99  --qbf_split                             512
% 2.03/0.99  
% 2.03/0.99  ------ BMC1 Options
% 2.03/0.99  
% 2.03/0.99  --bmc1_incremental                      false
% 2.03/0.99  --bmc1_axioms                           reachable_all
% 2.03/0.99  --bmc1_min_bound                        0
% 2.03/0.99  --bmc1_max_bound                        -1
% 2.03/0.99  --bmc1_max_bound_default                -1
% 2.03/0.99  --bmc1_symbol_reachability              true
% 2.03/0.99  --bmc1_property_lemmas                  false
% 2.03/0.99  --bmc1_k_induction                      false
% 2.03/0.99  --bmc1_non_equiv_states                 false
% 2.03/0.99  --bmc1_deadlock                         false
% 2.03/0.99  --bmc1_ucm                              false
% 2.03/0.99  --bmc1_add_unsat_core                   none
% 2.03/0.99  --bmc1_unsat_core_children              false
% 2.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.03/0.99  --bmc1_out_stat                         full
% 2.03/0.99  --bmc1_ground_init                      false
% 2.03/0.99  --bmc1_pre_inst_next_state              false
% 2.03/0.99  --bmc1_pre_inst_state                   false
% 2.03/0.99  --bmc1_pre_inst_reach_state             false
% 2.03/0.99  --bmc1_out_unsat_core                   false
% 2.03/0.99  --bmc1_aig_witness_out                  false
% 2.03/0.99  --bmc1_verbose                          false
% 2.03/0.99  --bmc1_dump_clauses_tptp                false
% 2.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.03/0.99  --bmc1_dump_file                        -
% 2.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.03/0.99  --bmc1_ucm_extend_mode                  1
% 2.03/0.99  --bmc1_ucm_init_mode                    2
% 2.03/0.99  --bmc1_ucm_cone_mode                    none
% 2.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.03/0.99  --bmc1_ucm_relax_model                  4
% 2.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.03/0.99  --bmc1_ucm_layered_model                none
% 2.03/0.99  --bmc1_ucm_max_lemma_size               10
% 2.03/0.99  
% 2.03/0.99  ------ AIG Options
% 2.03/0.99  
% 2.03/0.99  --aig_mode                              false
% 2.03/0.99  
% 2.03/0.99  ------ Instantiation Options
% 2.03/0.99  
% 2.03/0.99  --instantiation_flag                    true
% 2.03/0.99  --inst_sos_flag                         false
% 2.03/0.99  --inst_sos_phase                        true
% 2.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel_side                     none
% 2.03/0.99  --inst_solver_per_active                1400
% 2.03/0.99  --inst_solver_calls_frac                1.
% 2.03/0.99  --inst_passive_queue_type               priority_queues
% 2.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.03/0.99  --inst_passive_queues_freq              [25;2]
% 2.03/0.99  --inst_dismatching                      true
% 2.03/0.99  --inst_eager_unprocessed_to_passive     true
% 2.03/0.99  --inst_prop_sim_given                   true
% 2.03/0.99  --inst_prop_sim_new                     false
% 2.03/0.99  --inst_subs_new                         false
% 2.03/0.99  --inst_eq_res_simp                      false
% 2.03/0.99  --inst_subs_given                       false
% 2.03/0.99  --inst_orphan_elimination               true
% 2.03/0.99  --inst_learning_loop_flag               true
% 2.03/0.99  --inst_learning_start                   3000
% 2.03/0.99  --inst_learning_factor                  2
% 2.03/0.99  --inst_start_prop_sim_after_learn       3
% 2.03/0.99  --inst_sel_renew                        solver
% 2.03/0.99  --inst_lit_activity_flag                true
% 2.03/0.99  --inst_restr_to_given                   false
% 2.03/0.99  --inst_activity_threshold               500
% 2.03/0.99  --inst_out_proof                        true
% 2.03/0.99  
% 2.03/0.99  ------ Resolution Options
% 2.03/0.99  
% 2.03/0.99  --resolution_flag                       false
% 2.03/0.99  --res_lit_sel                           adaptive
% 2.03/0.99  --res_lit_sel_side                      none
% 2.03/0.99  --res_ordering                          kbo
% 2.03/0.99  --res_to_prop_solver                    active
% 2.03/0.99  --res_prop_simpl_new                    false
% 2.03/0.99  --res_prop_simpl_given                  true
% 2.03/0.99  --res_passive_queue_type                priority_queues
% 2.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.03/0.99  --res_passive_queues_freq               [15;5]
% 2.03/0.99  --res_forward_subs                      full
% 2.03/0.99  --res_backward_subs                     full
% 2.03/0.99  --res_forward_subs_resolution           true
% 2.03/0.99  --res_backward_subs_resolution          true
% 2.03/0.99  --res_orphan_elimination                true
% 2.03/0.99  --res_time_limit                        2.
% 2.03/0.99  --res_out_proof                         true
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Options
% 2.03/0.99  
% 2.03/0.99  --superposition_flag                    true
% 2.03/0.99  --sup_passive_queue_type                priority_queues
% 2.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.03/0.99  --demod_completeness_check              fast
% 2.03/0.99  --demod_use_ground                      true
% 2.03/0.99  --sup_to_prop_solver                    passive
% 2.03/0.99  --sup_prop_simpl_new                    true
% 2.03/0.99  --sup_prop_simpl_given                  true
% 2.03/0.99  --sup_fun_splitting                     false
% 2.03/0.99  --sup_smt_interval                      50000
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Simplification Setup
% 2.03/0.99  
% 2.03/0.99  --sup_indices_passive                   []
% 2.03/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_full_bw                           [BwDemod]
% 2.03/0.99  --sup_immed_triv                        [TrivRules]
% 2.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_immed_bw_main                     []
% 2.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  
% 2.03/0.99  ------ Combination Options
% 2.03/0.99  
% 2.03/0.99  --comb_res_mult                         3
% 2.03/0.99  --comb_sup_mult                         2
% 2.03/0.99  --comb_inst_mult                        10
% 2.03/0.99  
% 2.03/0.99  ------ Debug Options
% 2.03/0.99  
% 2.03/0.99  --dbg_backtrace                         false
% 2.03/0.99  --dbg_dump_prop_clauses                 false
% 2.03/0.99  --dbg_dump_prop_clauses_file            -
% 2.03/0.99  --dbg_out_stat                          false
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  ------ Proving...
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 2.03/0.99  
% 2.03/0.99  % SZS output start Saturation for theBenchmark.p
% 2.03/0.99  
% 2.03/0.99  fof(f4,axiom,(
% 2.03/0.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f25,plain,(
% 2.03/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.03/0.99    inference(nnf_transformation,[],[f4])).
% 2.03/0.99  
% 2.03/0.99  fof(f26,plain,(
% 2.03/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.03/0.99    inference(rectify,[],[f25])).
% 2.03/0.99  
% 2.03/0.99  fof(f27,plain,(
% 2.03/0.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f28,plain,(
% 2.03/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 2.03/0.99  
% 2.03/0.99  fof(f38,plain,(
% 2.03/0.99    ( ! [X0,X1] : (k1_zfmisc_1(X0) = X1 | r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f28])).
% 2.03/0.99  
% 2.03/0.99  fof(f36,plain,(
% 2.03/0.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.03/0.99    inference(cnf_transformation,[],[f28])).
% 2.03/0.99  
% 2.03/0.99  fof(f47,plain,(
% 2.03/0.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.03/0.99    inference(equality_resolution,[],[f36])).
% 2.03/0.99  
% 2.03/0.99  fof(f37,plain,(
% 2.03/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 2.03/0.99    inference(cnf_transformation,[],[f28])).
% 2.03/0.99  
% 2.03/0.99  fof(f46,plain,(
% 2.03/0.99    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 2.03/0.99    inference(equality_resolution,[],[f37])).
% 2.03/0.99  
% 2.03/0.99  fof(f2,axiom,(
% 2.03/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f11,plain,(
% 2.03/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.03/0.99    inference(rectify,[],[f2])).
% 2.03/0.99  
% 2.03/0.99  fof(f15,plain,(
% 2.03/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.03/0.99    inference(ennf_transformation,[],[f11])).
% 2.03/0.99  
% 2.03/0.99  fof(f23,plain,(
% 2.03/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f24,plain,(
% 2.03/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f23])).
% 2.03/0.99  
% 2.03/0.99  fof(f34,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f24])).
% 2.03/0.99  
% 2.03/0.99  fof(f3,axiom,(
% 2.03/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f16,plain,(
% 2.03/0.99    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.03/0.99    inference(ennf_transformation,[],[f3])).
% 2.03/0.99  
% 2.03/0.99  fof(f17,plain,(
% 2.03/0.99    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.03/0.99    inference(flattening,[],[f16])).
% 2.03/0.99  
% 2.03/0.99  fof(f35,plain,(
% 2.03/0.99    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f17])).
% 2.03/0.99  
% 2.03/0.99  fof(f32,plain,(
% 2.03/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f24])).
% 2.03/0.99  
% 2.03/0.99  fof(f33,plain,(
% 2.03/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f24])).
% 2.03/0.99  
% 2.03/0.99  fof(f7,axiom,(
% 2.03/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f19,plain,(
% 2.03/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.03/0.99    inference(ennf_transformation,[],[f7])).
% 2.03/0.99  
% 2.03/0.99  fof(f20,plain,(
% 2.03/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.03/0.99    inference(flattening,[],[f19])).
% 2.03/0.99  
% 2.03/0.99  fof(f42,plain,(
% 2.03/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f20])).
% 2.03/0.99  
% 2.03/0.99  fof(f9,conjecture,(
% 2.03/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r2_hidden(X2,X1)) & k1_struct_0(X0) != X1)))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f10,negated_conjecture,(
% 2.03/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r2_hidden(X2,X1)) & k1_struct_0(X0) != X1)))),
% 2.03/0.99    inference(negated_conjecture,[],[f9])).
% 2.03/0.99  
% 2.03/0.99  fof(f13,plain,(
% 2.03/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r2_hidden(X2,X1)) & k1_struct_0(X0) != X1))),
% 2.03/0.99    inference(pure_predicate_removal,[],[f10])).
% 2.03/0.99  
% 2.03/0.99  fof(f21,plain,(
% 2.03/0.99    ? [X0,X1] : ((! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & k1_struct_0(X0) != X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 2.03/0.99    inference(ennf_transformation,[],[f13])).
% 2.03/0.99  
% 2.03/0.99  fof(f22,plain,(
% 2.03/0.99    ? [X0,X1] : (! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & k1_struct_0(X0) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 2.03/0.99    inference(flattening,[],[f21])).
% 2.03/0.99  
% 2.03/0.99  fof(f29,plain,(
% 2.03/0.99    ? [X0,X1] : (! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & k1_struct_0(X0) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X2] : (~r2_hidden(X2,sK3) | ~m1_subset_1(X2,u1_struct_0(sK2))) & k1_struct_0(sK2) != sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f30,plain,(
% 2.03/0.99    ! [X2] : (~r2_hidden(X2,sK3) | ~m1_subset_1(X2,u1_struct_0(sK2))) & k1_struct_0(sK2) != sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f22,f29])).
% 2.03/0.99  
% 2.03/0.99  fof(f43,plain,(
% 2.03/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.03/0.99    inference(cnf_transformation,[],[f30])).
% 2.03/0.99  
% 2.03/0.99  fof(f5,axiom,(
% 2.03/0.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f40,plain,(
% 2.03/0.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.03/0.99    inference(cnf_transformation,[],[f5])).
% 2.03/0.99  
% 2.03/0.99  fof(f6,axiom,(
% 2.03/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f18,plain,(
% 2.03/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.03/0.99    inference(ennf_transformation,[],[f6])).
% 2.03/0.99  
% 2.03/0.99  fof(f41,plain,(
% 2.03/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f18])).
% 2.03/0.99  
% 2.03/0.99  fof(f45,plain,(
% 2.03/0.99    ( ! [X2] : (~r2_hidden(X2,sK3) | ~m1_subset_1(X2,u1_struct_0(sK2))) )),
% 2.03/0.99    inference(cnf_transformation,[],[f30])).
% 2.03/0.99  
% 2.03/0.99  fof(f1,axiom,(
% 2.03/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f14,plain,(
% 2.03/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.03/0.99    inference(ennf_transformation,[],[f1])).
% 2.03/0.99  
% 2.03/0.99  fof(f31,plain,(
% 2.03/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f14])).
% 2.03/0.99  
% 2.03/0.99  fof(f44,plain,(
% 2.03/0.99    k1_struct_0(sK2) != sK3),
% 2.03/0.99    inference(cnf_transformation,[],[f30])).
% 2.03/0.99  
% 2.03/0.99  fof(f39,plain,(
% 2.03/0.99    ( ! [X0,X1] : (k1_zfmisc_1(X0) = X1 | ~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f28])).
% 2.03/0.99  
% 2.03/0.99  cnf(c_185,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.03/0.99      theory(equality) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_701,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_6,plain,
% 2.03/0.99      ( r1_tarski(sK1(X0,X1),X0)
% 2.03/0.99      | r2_hidden(sK1(X0,X1),X1)
% 2.03/0.99      | k1_zfmisc_1(X0) = X1 ),
% 2.03/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1050,plain,
% 2.03/0.99      ( k1_zfmisc_1(X0) = X1
% 2.03/0.99      | r1_tarski(sK1(X0,X1),X0) = iProver_top
% 2.03/0.99      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_8,plain,
% 2.03/0.99      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.03/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1048,plain,
% 2.03/0.99      ( r1_tarski(X0,X1) = iProver_top
% 2.03/0.99      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1557,plain,
% 2.03/0.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 2.03/0.99      | r1_tarski(sK1(X1,k1_zfmisc_1(X0)),X1) = iProver_top
% 2.03/0.99      | r1_tarski(sK1(X1,k1_zfmisc_1(X0)),X0) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1050,c_1048]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_7,plain,
% 2.03/0.99      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.03/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1049,plain,
% 2.03/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.03/0.99      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1,plain,
% 2.03/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 2.03/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1055,plain,
% 2.03/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.03/0.99      | r2_hidden(X0,X2) != iProver_top
% 2.03/0.99      | r1_xboole_0(X2,X1) != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2003,plain,
% 2.03/0.99      ( k1_zfmisc_1(X0) = X1
% 2.03/0.99      | r1_tarski(sK1(X0,X1),X0) = iProver_top
% 2.03/0.99      | r2_hidden(sK1(X0,X1),X2) != iProver_top
% 2.03/0.99      | r1_xboole_0(X2,X1) != iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1050,c_1055]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3161,plain,
% 2.03/0.99      ( k1_zfmisc_1(X0) = X1
% 2.03/0.99      | r1_tarski(sK1(X0,X1),X2) != iProver_top
% 2.03/0.99      | r1_tarski(sK1(X0,X1),X0) = iProver_top
% 2.03/0.99      | r1_xboole_0(k1_zfmisc_1(X2),X1) != iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1049,c_2003]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3282,plain,
% 2.03/0.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 2.03/0.99      | r1_tarski(sK1(X0,k1_zfmisc_1(X1)),X0) = iProver_top
% 2.03/0.99      | r1_tarski(sK1(X0,k1_zfmisc_1(X1)),X1) = iProver_top
% 2.03/0.99      | r1_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) != iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1557,c_3161]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_4,plain,
% 2.03/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1052,plain,
% 2.03/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.03/0.99      | r1_xboole_0(X0,X1) != iProver_top
% 2.03/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3402,plain,
% 2.03/0.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 2.03/0.99      | r1_tarski(sK1(X1,k1_zfmisc_1(X0)),X0) = iProver_top
% 2.03/0.99      | r1_xboole_0(sK1(X1,k1_zfmisc_1(X0)),X1) != iProver_top
% 2.03/0.99      | r1_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X0)) != iProver_top
% 2.03/0.99      | v1_xboole_0(sK1(X1,k1_zfmisc_1(X0))) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_3282,c_1052]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3399,plain,
% 2.03/0.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 2.03/0.99      | r1_tarski(sK1(X1,k1_zfmisc_1(X0)),X1) = iProver_top
% 2.03/0.99      | r1_xboole_0(sK1(X1,k1_zfmisc_1(X0)),X0) != iProver_top
% 2.03/0.99      | r1_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X0)) != iProver_top
% 2.03/0.99      | v1_xboole_0(sK1(X1,k1_zfmisc_1(X0))) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_3282,c_1052]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3160,plain,
% 2.03/0.99      ( k1_zfmisc_1(X0) = X1
% 2.03/0.99      | r1_tarski(sK1(X0,X1),X0) = iProver_top
% 2.03/0.99      | r1_xboole_0(X1,X1) != iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1050,c_2003]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3,plain,
% 2.03/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 2.03/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1053,plain,
% 2.03/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.03/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2002,plain,
% 2.03/0.99      ( r2_hidden(sK0(X0,X1),X2) != iProver_top
% 2.03/0.99      | r1_xboole_0(X2,X0) != iProver_top
% 2.03/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1053,c_1055]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2770,plain,
% 2.03/0.99      ( r1_tarski(sK0(X0,X1),X2) != iProver_top
% 2.03/0.99      | r1_xboole_0(X0,X1) = iProver_top
% 2.03/0.99      | r1_xboole_0(k1_zfmisc_1(X2),X0) != iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1049,c_2002]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2769,plain,
% 2.03/0.99      ( r1_xboole_0(X0,X0) != iProver_top | r1_xboole_0(X0,X1) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1053,c_2002]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2,plain,
% 2.03/0.99      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 2.03/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1054,plain,
% 2.03/0.99      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 2.03/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2768,plain,
% 2.03/0.99      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1054,c_2002]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2001,plain,
% 2.03/0.99      ( r2_hidden(sK0(X0,X1),X2) != iProver_top
% 2.03/0.99      | r1_xboole_0(X2,X1) != iProver_top
% 2.03/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1054,c_1055]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2570,plain,
% 2.03/0.99      ( r1_tarski(sK0(X0,X1),X2) != iProver_top
% 2.03/0.99      | r1_xboole_0(X0,X1) = iProver_top
% 2.03/0.99      | r1_xboole_0(k1_zfmisc_1(X2),X1) != iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1049,c_2001]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2568,plain,
% 2.03/0.99      ( r1_xboole_0(X0,X0) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1054,c_2001]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2508,plain,
% 2.03/0.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 2.03/0.99      | r1_tarski(sK1(X0,k1_zfmisc_1(X1)),X1) = iProver_top
% 2.03/0.99      | r1_xboole_0(sK1(X0,k1_zfmisc_1(X1)),X0) != iProver_top
% 2.03/0.99      | v1_xboole_0(sK1(X0,k1_zfmisc_1(X1))) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1557,c_1052]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2506,plain,
% 2.03/0.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 2.03/0.99      | r1_tarski(sK1(X0,k1_zfmisc_1(X1)),X0) = iProver_top
% 2.03/0.99      | r1_xboole_0(sK1(X0,k1_zfmisc_1(X1)),X1) != iProver_top
% 2.03/0.99      | v1_xboole_0(sK1(X0,k1_zfmisc_1(X1))) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1557,c_1052]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_11,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.03/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_14,negated_conjecture,
% 2.03/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.03/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_215,plain,
% 2.03/0.99      ( r2_hidden(X0,X1)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | k1_zfmisc_1(u1_struct_0(sK2)) != X1
% 2.03/0.99      | sK3 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_14]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_216,plain,
% 2.03/0.99      ( r2_hidden(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.03/0.99      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_215]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_9,plain,
% 2.03/0.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 2.03/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_222,plain,
% 2.03/0.99      ( r2_hidden(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.03/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_216,c_9]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1045,plain,
% 2.03/0.99      ( r2_hidden(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1317,plain,
% 2.03/0.99      ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1045,c_1048]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1488,plain,
% 2.03/0.99      ( r1_xboole_0(sK3,u1_struct_0(sK2)) != iProver_top
% 2.03/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1317,c_1052]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_224,plain,
% 2.03/0.99      ( r2_hidden(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1144,plain,
% 2.03/0.99      ( r1_tarski(sK3,u1_struct_0(sK2))
% 2.03/0.99      | ~ r2_hidden(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1145,plain,
% 2.03/0.99      ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top
% 2.03/0.99      | r2_hidden(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_1144]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1170,plain,
% 2.03/0.99      ( ~ r1_tarski(sK3,u1_struct_0(sK2))
% 2.03/0.99      | ~ r1_xboole_0(sK3,u1_struct_0(sK2))
% 2.03/0.99      | v1_xboole_0(sK3) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1177,plain,
% 2.03/0.99      ( r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top
% 2.03/0.99      | r1_xboole_0(sK3,u1_struct_0(sK2)) != iProver_top
% 2.03/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_1170]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_10,plain,
% 2.03/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.03/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_12,negated_conjecture,
% 2.03/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2)) | ~ r2_hidden(X0,sK3) ),
% 2.03/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_203,plain,
% 2.03/0.99      ( ~ r2_hidden(X0,X1)
% 2.03/0.99      | ~ r2_hidden(X2,sK3)
% 2.03/0.99      | X2 != X0
% 2.03/0.99      | u1_struct_0(sK2) != X1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_12]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_204,plain,
% 2.03/0.99      ( ~ r2_hidden(X0,u1_struct_0(sK2)) | ~ r2_hidden(X0,sK3) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_203]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1046,plain,
% 2.03/0.99      ( r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
% 2.03/0.99      | r2_hidden(X0,sK3) != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_204]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1469,plain,
% 2.03/0.99      ( r2_hidden(sK0(X0,u1_struct_0(sK2)),sK3) != iProver_top
% 2.03/0.99      | r1_xboole_0(X0,u1_struct_0(sK2)) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1054,c_1046]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1667,plain,
% 2.03/0.99      ( r1_xboole_0(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1053,c_1469]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1785,plain,
% 2.03/0.99      ( v1_xboole_0(sK3) = iProver_top ),
% 2.03/0.99      inference(global_propositional_subsumption,
% 2.03/0.99                [status(thm)],
% 2.03/0.99                [c_1488,c_224,c_1145,c_1177,c_1667]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_0,plain,
% 2.03/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.03/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1056,plain,
% 2.03/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1790,plain,
% 2.03/0.99      ( sK3 = k1_xboole_0 ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1785,c_1056]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1799,plain,
% 2.03/0.99      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.03/0.99      inference(demodulation,[status(thm)],[c_1790,c_1045]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2203,plain,
% 2.03/0.99      ( r2_hidden(k1_xboole_0,X0) != iProver_top
% 2.03/0.99      | r1_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1799,c_1055]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1468,plain,
% 2.03/0.99      ( r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1) = iProver_top
% 2.03/0.99      | r1_xboole_0(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1054,c_1048]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2131,plain,
% 2.03/0.99      ( r1_xboole_0(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.03/0.99      | r1_xboole_0(sK0(X0,k1_zfmisc_1(X1)),X1) != iProver_top
% 2.03/0.99      | v1_xboole_0(sK0(X0,k1_zfmisc_1(X1))) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1468,c_1052]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1386,plain,
% 2.03/0.99      ( r1_tarski(sK0(k1_zfmisc_1(X0),X1),X0) = iProver_top
% 2.03/0.99      | r1_xboole_0(k1_zfmisc_1(X0),X1) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1053,c_1048]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2042,plain,
% 2.03/0.99      ( r1_xboole_0(sK0(k1_zfmisc_1(X0),X1),X0) != iProver_top
% 2.03/0.99      | r1_xboole_0(k1_zfmisc_1(X0),X1) = iProver_top
% 2.03/0.99      | v1_xboole_0(sK0(k1_zfmisc_1(X0),X1)) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1386,c_1052]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2004,plain,
% 2.03/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.03/0.99      | r2_hidden(X0,X2) != iProver_top
% 2.03/0.99      | r1_xboole_0(X2,k1_zfmisc_1(X1)) != iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1049,c_1055]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_13,negated_conjecture,
% 2.03/0.99      ( k1_struct_0(sK2) != sK3 ),
% 2.03/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1802,plain,
% 2.03/0.99      ( k1_struct_0(sK2) != k1_xboole_0 ),
% 2.03/0.99      inference(demodulation,[status(thm)],[c_1790,c_13]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_225,plain,
% 2.03/0.99      ( ~ r2_hidden(X0,sK3)
% 2.03/0.99      | k1_zfmisc_1(u1_struct_0(sK2)) != u1_struct_0(sK2)
% 2.03/0.99      | sK3 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_226,plain,
% 2.03/0.99      ( ~ r2_hidden(sK3,sK3)
% 2.03/0.99      | k1_zfmisc_1(u1_struct_0(sK2)) != u1_struct_0(sK2) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_225]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1044,plain,
% 2.03/0.99      ( k1_zfmisc_1(u1_struct_0(sK2)) != u1_struct_0(sK2)
% 2.03/0.99      | r2_hidden(sK3,sK3) != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1801,plain,
% 2.03/0.99      ( k1_zfmisc_1(u1_struct_0(sK2)) != u1_struct_0(sK2)
% 2.03/0.99      | r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.03/0.99      inference(demodulation,[status(thm)],[c_1790,c_1044]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1800,plain,
% 2.03/0.99      ( r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
% 2.03/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.03/0.99      inference(demodulation,[status(thm)],[c_1790,c_1046]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1798,plain,
% 2.03/0.99      ( r1_tarski(k1_xboole_0,u1_struct_0(sK2)) = iProver_top ),
% 2.03/0.99      inference(demodulation,[status(thm)],[c_1790,c_1317]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1387,plain,
% 2.03/0.99      ( r2_hidden(sK0(u1_struct_0(sK2),X0),sK3) != iProver_top
% 2.03/0.99      | r1_xboole_0(u1_struct_0(sK2),X0) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1053,c_1046]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1797,plain,
% 2.03/0.99      ( r2_hidden(sK0(u1_struct_0(sK2),X0),k1_xboole_0) != iProver_top
% 2.03/0.99      | r1_xboole_0(u1_struct_0(sK2),X0) = iProver_top ),
% 2.03/0.99      inference(demodulation,[status(thm)],[c_1790,c_1387]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1796,plain,
% 2.03/0.99      ( r2_hidden(sK0(X0,u1_struct_0(sK2)),k1_xboole_0) != iProver_top
% 2.03/0.99      | r1_xboole_0(X0,u1_struct_0(sK2)) = iProver_top ),
% 2.03/0.99      inference(demodulation,[status(thm)],[c_1790,c_1469]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1558,plain,
% 2.03/0.99      ( k1_zfmisc_1(X0) = u1_struct_0(sK2)
% 2.03/0.99      | r1_tarski(sK1(X0,u1_struct_0(sK2)),X0) = iProver_top
% 2.03/0.99      | r2_hidden(sK1(X0,u1_struct_0(sK2)),sK3) != iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1050,c_1046]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1795,plain,
% 2.03/0.99      ( k1_zfmisc_1(X0) = u1_struct_0(sK2)
% 2.03/0.99      | r1_tarski(sK1(X0,u1_struct_0(sK2)),X0) = iProver_top
% 2.03/0.99      | r2_hidden(sK1(X0,u1_struct_0(sK2)),k1_xboole_0) != iProver_top ),
% 2.03/0.99      inference(demodulation,[status(thm)],[c_1790,c_1558]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1590,plain,
% 2.03/0.99      ( r1_xboole_0(u1_struct_0(sK2),sK3) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1054,c_1387]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1794,plain,
% 2.03/0.99      ( r1_xboole_0(u1_struct_0(sK2),k1_xboole_0) = iProver_top ),
% 2.03/0.99      inference(demodulation,[status(thm)],[c_1790,c_1590]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1793,plain,
% 2.03/0.99      ( r1_xboole_0(k1_xboole_0,u1_struct_0(sK2)) = iProver_top ),
% 2.03/0.99      inference(demodulation,[status(thm)],[c_1790,c_1667]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1792,plain,
% 2.03/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.03/0.99      inference(demodulation,[status(thm)],[c_1790,c_1785]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1559,plain,
% 2.03/0.99      ( k1_zfmisc_1(X0) = X1
% 2.03/0.99      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 2.03/0.99      | r1_xboole_0(sK1(X0,X1),X0) != iProver_top
% 2.03/0.99      | v1_xboole_0(sK1(X0,X1)) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1050,c_1052]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_5,plain,
% 2.03/0.99      ( ~ r1_tarski(sK1(X0,X1),X0)
% 2.03/0.99      | ~ r2_hidden(sK1(X0,X1),X1)
% 2.03/0.99      | k1_zfmisc_1(X0) = X1 ),
% 2.03/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1051,plain,
% 2.03/0.99      ( k1_zfmisc_1(X0) = X1
% 2.03/0.99      | r1_tarski(sK1(X0,X1),X0) != iProver_top
% 2.03/0.99      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1047,plain,
% 2.03/0.99      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  % SZS output end Saturation for theBenchmark.p
% 2.03/0.99  
% 2.03/0.99  ------                               Statistics
% 2.03/0.99  
% 2.03/0.99  ------ General
% 2.03/0.99  
% 2.03/0.99  abstr_ref_over_cycles:                  0
% 2.03/0.99  abstr_ref_under_cycles:                 0
% 2.03/0.99  gc_basic_clause_elim:                   0
% 2.03/0.99  forced_gc_time:                         0
% 2.03/0.99  parsing_time:                           0.008
% 2.03/0.99  unif_index_cands_time:                  0.
% 2.03/0.99  unif_index_add_time:                    0.
% 2.03/0.99  orderings_time:                         0.
% 2.03/0.99  out_proof_time:                         0.
% 2.03/0.99  total_time:                             0.129
% 2.03/0.99  num_of_symbols:                         44
% 2.03/0.99  num_of_terms:                           2521
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing
% 2.03/0.99  
% 2.03/0.99  num_of_splits:                          0
% 2.03/0.99  num_of_split_atoms:                     0
% 2.03/0.99  num_of_reused_defs:                     0
% 2.03/0.99  num_eq_ax_congr_red:                    21
% 2.03/0.99  num_of_sem_filtered_clauses:            1
% 2.03/0.99  num_of_subtypes:                        0
% 2.03/0.99  monotx_restored_types:                  0
% 2.03/0.99  sat_num_of_epr_types:                   0
% 2.03/0.99  sat_num_of_non_cyclic_types:            0
% 2.03/0.99  sat_guarded_non_collapsed_types:        0
% 2.03/0.99  num_pure_diseq_elim:                    0
% 2.03/0.99  simp_replaced_by:                       0
% 2.03/0.99  res_preprocessed:                       74
% 2.03/0.99  prep_upred:                             0
% 2.03/0.99  prep_unflattend:                        27
% 2.03/0.99  smt_new_axioms:                         0
% 2.03/0.99  pred_elim_cands:                        4
% 2.03/0.99  pred_elim:                              1
% 2.03/0.99  pred_elim_cl:                           1
% 2.03/0.99  pred_elim_cycles:                       7
% 2.03/0.99  merged_defs:                            8
% 2.03/0.99  merged_defs_ncl:                        0
% 2.03/0.99  bin_hyper_res:                          8
% 2.03/0.99  prep_cycles:                            4
% 2.03/0.99  pred_elim_time:                         0.004
% 2.03/0.99  splitting_time:                         0.
% 2.03/0.99  sem_filter_time:                        0.
% 2.03/0.99  monotx_time:                            0.001
% 2.03/0.99  subtype_inf_time:                       0.
% 2.03/0.99  
% 2.03/0.99  ------ Problem properties
% 2.03/0.99  
% 2.03/0.99  clauses:                                14
% 2.03/0.99  conjectures:                            1
% 2.03/0.99  epr:                                    3
% 2.03/0.99  horn:                                   11
% 2.03/0.99  ground:                                 3
% 2.03/0.99  unary:                                  3
% 2.03/0.99  binary:                                 7
% 2.03/0.99  lits:                                   29
% 2.03/0.99  lits_eq:                                5
% 2.03/0.99  fd_pure:                                0
% 2.03/0.99  fd_pseudo:                              0
% 2.03/0.99  fd_cond:                                1
% 2.03/0.99  fd_pseudo_cond:                         2
% 2.03/0.99  ac_symbols:                             0
% 2.03/0.99  
% 2.03/0.99  ------ Propositional Solver
% 2.03/0.99  
% 2.03/0.99  prop_solver_calls:                      30
% 2.03/0.99  prop_fast_solver_calls:                 526
% 2.03/0.99  smt_solver_calls:                       0
% 2.03/0.99  smt_fast_solver_calls:                  0
% 2.03/0.99  prop_num_of_clauses:                    1192
% 2.03/0.99  prop_preprocess_simplified:             3787
% 2.03/0.99  prop_fo_subsumed:                       1
% 2.03/0.99  prop_solver_time:                       0.
% 2.03/0.99  smt_solver_time:                        0.
% 2.03/0.99  smt_fast_solver_time:                   0.
% 2.03/0.99  prop_fast_solver_time:                  0.
% 2.03/0.99  prop_unsat_core_time:                   0.
% 2.03/0.99  
% 2.03/0.99  ------ QBF
% 2.03/0.99  
% 2.03/0.99  qbf_q_res:                              0
% 2.03/0.99  qbf_num_tautologies:                    0
% 2.03/0.99  qbf_prep_cycles:                        0
% 2.03/0.99  
% 2.03/0.99  ------ BMC1
% 2.03/0.99  
% 2.03/0.99  bmc1_current_bound:                     -1
% 2.03/0.99  bmc1_last_solved_bound:                 -1
% 2.03/0.99  bmc1_unsat_core_size:                   -1
% 2.03/0.99  bmc1_unsat_core_parents_size:           -1
% 2.03/0.99  bmc1_merge_next_fun:                    0
% 2.03/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.03/0.99  
% 2.03/0.99  ------ Instantiation
% 2.03/0.99  
% 2.03/0.99  inst_num_of_clauses:                    370
% 2.03/0.99  inst_num_in_passive:                    104
% 2.03/0.99  inst_num_in_active:                     221
% 2.03/0.99  inst_num_in_unprocessed:                45
% 2.03/0.99  inst_num_of_loops:                      290
% 2.03/0.99  inst_num_of_learning_restarts:          0
% 2.03/0.99  inst_num_moves_active_passive:          64
% 2.03/0.99  inst_lit_activity:                      0
% 2.03/0.99  inst_lit_activity_moves:                0
% 2.03/0.99  inst_num_tautologies:                   0
% 2.03/0.99  inst_num_prop_implied:                  0
% 2.03/0.99  inst_num_existing_simplified:           0
% 2.03/0.99  inst_num_eq_res_simplified:             0
% 2.03/0.99  inst_num_child_elim:                    0
% 2.03/0.99  inst_num_of_dismatching_blockings:      95
% 2.03/0.99  inst_num_of_non_proper_insts:           350
% 2.03/0.99  inst_num_of_duplicates:                 0
% 2.03/0.99  inst_inst_num_from_inst_to_res:         0
% 2.03/0.99  inst_dismatching_checking_time:         0.
% 2.03/0.99  
% 2.03/0.99  ------ Resolution
% 2.03/0.99  
% 2.03/0.99  res_num_of_clauses:                     0
% 2.03/0.99  res_num_in_passive:                     0
% 2.03/0.99  res_num_in_active:                      0
% 2.03/0.99  res_num_of_loops:                       78
% 2.03/0.99  res_forward_subset_subsumed:            71
% 2.03/0.99  res_backward_subset_subsumed:           0
% 2.03/0.99  res_forward_subsumed:                   0
% 2.03/0.99  res_backward_subsumed:                  0
% 2.03/0.99  res_forward_subsumption_resolution:     1
% 2.03/0.99  res_backward_subsumption_resolution:    0
% 2.03/0.99  res_clause_to_clause_subsumption:       224
% 2.03/0.99  res_orphan_elimination:                 0
% 2.03/0.99  res_tautology_del:                      76
% 2.03/0.99  res_num_eq_res_simplified:              0
% 2.03/0.99  res_num_sel_changes:                    0
% 2.03/0.99  res_moves_from_active_to_pass:          0
% 2.03/0.99  
% 2.03/0.99  ------ Superposition
% 2.03/0.99  
% 2.03/0.99  sup_time_total:                         0.
% 2.03/0.99  sup_time_generating:                    0.
% 2.03/0.99  sup_time_sim_full:                      0.
% 2.03/0.99  sup_time_sim_immed:                     0.
% 2.03/0.99  
% 2.03/0.99  sup_num_of_clauses:                     48
% 2.03/0.99  sup_num_in_active:                      45
% 2.03/0.99  sup_num_in_passive:                     3
% 2.03/0.99  sup_num_of_loops:                       56
% 2.03/0.99  sup_fw_superposition:                   31
% 2.03/0.99  sup_bw_superposition:                   25
% 2.03/0.99  sup_immediate_simplified:               9
% 2.03/0.99  sup_given_eliminated:                   0
% 2.03/0.99  comparisons_done:                       0
% 2.03/0.99  comparisons_avoided:                    0
% 2.03/0.99  
% 2.03/0.99  ------ Simplifications
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  sim_fw_subset_subsumed:                 3
% 2.03/0.99  sim_bw_subset_subsumed:                 0
% 2.03/0.99  sim_fw_subsumed:                        6
% 2.03/0.99  sim_bw_subsumed:                        0
% 2.03/0.99  sim_fw_subsumption_res:                 1
% 2.03/0.99  sim_bw_subsumption_res:                 0
% 2.03/0.99  sim_tautology_del:                      4
% 2.03/0.99  sim_eq_tautology_del:                   5
% 2.03/0.99  sim_eq_res_simp:                        0
% 2.03/0.99  sim_fw_demodulated:                     0
% 2.03/0.99  sim_bw_demodulated:                     11
% 2.03/0.99  sim_light_normalised:                   0
% 2.03/0.99  sim_joinable_taut:                      0
% 2.03/0.99  sim_joinable_simp:                      0
% 2.03/0.99  sim_ac_normalised:                      0
% 2.03/0.99  sim_smt_subsumption:                    0
% 2.03/0.99  
%------------------------------------------------------------------------------

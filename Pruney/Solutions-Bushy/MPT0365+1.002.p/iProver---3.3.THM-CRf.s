%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0365+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:07 EST 2020

% Result     : Theorem 39.21s
% Output     : CNFRefutation 39.21s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 484 expanded)
%              Number of clauses        :   87 ( 183 expanded)
%              Number of leaves         :   13 ( 110 expanded)
%              Depth                    :   19
%              Number of atoms          :  400 (2329 expanded)
%              Number of equality atoms :  198 ( 626 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
              & r1_xboole_0(X1,X2) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
                & r1_xboole_0(X1,X2) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( k3_subset_1(X0,sK4) != X1
        & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,sK4))
        & r1_xboole_0(X1,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
            & r1_xboole_0(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k3_subset_1(sK2,X2) != sK3
          & r1_xboole_0(k3_subset_1(sK2,sK3),k3_subset_1(sK2,X2))
          & r1_xboole_0(sK3,X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k3_subset_1(sK2,sK4) != sK3
    & r1_xboole_0(k3_subset_1(sK2,sK3),k3_subset_1(sK2,sK4))
    & r1_xboole_0(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f23,f22])).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    r1_xboole_0(k3_subset_1(sK2,sK3),k3_subset_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
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

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

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
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f20])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    k3_subset_1(sK2,sK4) != sK3 ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    r1_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_540,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_529,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_543,plain,
    ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1021,plain,
    ( k4_xboole_0(sK2,sK4) = k3_subset_1(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_529,c_543])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_539,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1858,plain,
    ( r2_hidden(X0,k3_subset_1(sK2,sK4)) = iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1021,c_539])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_528,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1022,plain,
    ( k4_xboole_0(sK2,sK3) = k3_subset_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_528,c_543])).

cnf(c_1859,plain,
    ( r2_hidden(X0,k3_subset_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1022,c_539])).

cnf(c_13,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(sK2,sK3),k3_subset_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_531,plain,
    ( r1_xboole_0(k3_subset_1(sK2,sK3),k3_subset_1(sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_534,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1698,plain,
    ( r2_hidden(X0,k3_subset_1(sK2,sK3)) != iProver_top
    | r2_hidden(X0,k3_subset_1(sK2,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_531,c_534])).

cnf(c_2752,plain,
    ( r2_hidden(X0,k3_subset_1(sK2,sK4)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1859,c_1698])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_537,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1262,plain,
    ( r2_hidden(X0,k3_subset_1(sK2,sK4)) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1021,c_537])).

cnf(c_3459,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,k3_subset_1(sK2,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2752,c_1262])).

cnf(c_3460,plain,
    ( r2_hidden(X0,k3_subset_1(sK2,sK4)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3459])).

cnf(c_3471,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1858,c_3460])).

cnf(c_7868,plain,
    ( k4_xboole_0(sK2,X0) = X1
    | r2_hidden(sK0(sK2,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK2,X0,X1),sK3) = iProver_top
    | r2_hidden(sK0(sK2,X0,X1),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_540,c_3471])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_541,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_144557,plain,
    ( k4_xboole_0(sK2,sK3) = X0
    | r2_hidden(sK0(sK2,sK3,X0),X0) = iProver_top
    | r2_hidden(sK0(sK2,sK3,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7868,c_541])).

cnf(c_145035,plain,
    ( k3_subset_1(sK2,sK3) = X0
    | r2_hidden(sK0(sK2,sK3,X0),X0) = iProver_top
    | r2_hidden(sK0(sK2,sK3,X0),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_144557,c_1022])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_536,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1139,plain,
    ( k4_xboole_0(X0,k3_subset_1(X0,X1)) = k3_subset_1(X0,k3_subset_1(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_536,c_543])).

cnf(c_9849,plain,
    ( k4_xboole_0(sK2,k3_subset_1(sK2,sK4)) = k3_subset_1(sK2,k3_subset_1(sK2,sK4)) ),
    inference(superposition,[status(thm)],[c_529,c_1139])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_535,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_828,plain,
    ( k3_subset_1(sK2,k3_subset_1(sK2,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_529,c_535])).

cnf(c_9855,plain,
    ( k4_xboole_0(sK2,k3_subset_1(sK2,sK4)) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_9849,c_828])).

cnf(c_10038,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_9855,c_537])).

cnf(c_147617,plain,
    ( k3_subset_1(sK2,sK3) = X0
    | r2_hidden(sK0(sK2,sK3,X0),X0) = iProver_top
    | r2_hidden(sK0(sK2,sK3,X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_145035,c_10038])).

cnf(c_154954,plain,
    ( k3_subset_1(sK2,sK3) = sK4
    | r2_hidden(sK0(sK2,sK3,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_147617,c_10038])).

cnf(c_147701,plain,
    ( k3_subset_1(sK2,sK3) = sK4
    | r2_hidden(sK0(sK2,sK3,sK4),sK4) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_145035])).

cnf(c_147703,plain,
    ( k3_subset_1(sK2,sK3) = sK4
    | r2_hidden(sK0(sK2,sK3,sK4),sK4) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_147701])).

cnf(c_238,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_894,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_238])).

cnf(c_1298,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_894])).

cnf(c_106826,plain,
    ( k3_subset_1(sK2,sK3) != sK4
    | sK4 = k3_subset_1(sK2,sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1298])).

cnf(c_1203,plain,
    ( X0 != X1
    | X0 = k3_subset_1(sK2,sK3)
    | k3_subset_1(sK2,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_238])).

cnf(c_8225,plain,
    ( X0 != k4_xboole_0(X1,X2)
    | X0 = k3_subset_1(sK2,sK3)
    | k3_subset_1(sK2,sK3) != k4_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1203])).

cnf(c_22442,plain,
    ( X0 != k4_xboole_0(sK2,sK3)
    | X0 = k3_subset_1(sK2,sK3)
    | k3_subset_1(sK2,sK3) != k4_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_8225])).

cnf(c_37215,plain,
    ( k3_subset_1(sK2,sK3) != k4_xboole_0(sK2,sK3)
    | sK4 != k4_xboole_0(sK2,sK3)
    | sK4 = k3_subset_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_22442])).

cnf(c_3885,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(X2,X3)
    | k4_xboole_0(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_238])).

cnf(c_8203,plain,
    ( k4_xboole_0(X0,X1) != X2
    | sK4 != X2
    | sK4 = k4_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_3885])).

cnf(c_15652,plain,
    ( k4_xboole_0(X0,X1) != sK4
    | sK4 = k4_xboole_0(X0,X1)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_8203])).

cnf(c_37214,plain,
    ( k4_xboole_0(sK2,sK3) != sK4
    | sK4 = k4_xboole_0(sK2,sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_15652])).

cnf(c_1380,plain,
    ( ~ r1_xboole_0(X0,sK4)
    | ~ r2_hidden(sK0(X1,X2,sK4),X0)
    | ~ r2_hidden(sK0(X1,X2,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2228,plain,
    ( ~ r1_xboole_0(sK3,sK4)
    | ~ r2_hidden(sK0(X0,X1,sK4),sK3)
    | ~ r2_hidden(sK0(X0,X1,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1380])).

cnf(c_14666,plain,
    ( ~ r1_xboole_0(sK3,sK4)
    | ~ r2_hidden(sK0(X0,sK3,sK4),sK3)
    | ~ r2_hidden(sK0(X0,sK3,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_2228])).

cnf(c_14671,plain,
    ( r1_xboole_0(sK3,sK4) != iProver_top
    | r2_hidden(sK0(X0,sK3,sK4),sK3) != iProver_top
    | r2_hidden(sK0(X0,sK3,sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14666])).

cnf(c_14673,plain,
    ( r1_xboole_0(sK3,sK4) != iProver_top
    | r2_hidden(sK0(sK2,sK3,sK4),sK3) != iProver_top
    | r2_hidden(sK0(sK2,sK3,sK4),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14671])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_722,plain,
    ( ~ r2_hidden(sK0(X0,X1,sK4),X0)
    | r2_hidden(sK0(X0,X1,sK4),X1)
    | ~ r2_hidden(sK0(X0,X1,sK4),sK4)
    | k4_xboole_0(X0,X1) = sK4 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_14665,plain,
    ( ~ r2_hidden(sK0(X0,sK3,sK4),X0)
    | r2_hidden(sK0(X0,sK3,sK4),sK3)
    | ~ r2_hidden(sK0(X0,sK3,sK4),sK4)
    | k4_xboole_0(X0,sK3) = sK4 ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_14667,plain,
    ( k4_xboole_0(X0,sK3) = sK4
    | r2_hidden(sK0(X0,sK3,sK4),X0) != iProver_top
    | r2_hidden(sK0(X0,sK3,sK4),sK3) = iProver_top
    | r2_hidden(sK0(X0,sK3,sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14665])).

cnf(c_14669,plain,
    ( k4_xboole_0(sK2,sK3) = sK4
    | r2_hidden(sK0(sK2,sK3,sK4),sK3) = iProver_top
    | r2_hidden(sK0(sK2,sK3,sK4),sK4) != iProver_top
    | r2_hidden(sK0(sK2,sK3,sK4),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14667])).

cnf(c_2801,plain,
    ( X0 != X1
    | k3_subset_1(sK2,sK3) != X1
    | k3_subset_1(sK2,sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_238])).

cnf(c_6482,plain,
    ( X0 != k3_subset_1(sK2,sK3)
    | k3_subset_1(sK2,sK3) = X0
    | k3_subset_1(sK2,sK3) != k3_subset_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2801])).

cnf(c_12666,plain,
    ( k4_xboole_0(sK2,sK3) != k3_subset_1(sK2,sK3)
    | k3_subset_1(sK2,sK3) = k4_xboole_0(sK2,sK3)
    | k3_subset_1(sK2,sK3) != k3_subset_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_6482])).

cnf(c_237,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2079,plain,
    ( k3_subset_1(sK2,sK3) = k3_subset_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_239,plain,
    ( X0 != X1
    | X2 != X3
    | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
    theory(equality)).

cnf(c_1824,plain,
    ( k3_subset_1(sK2,sK4) = k3_subset_1(sK2,k3_subset_1(sK2,sK3))
    | sK4 != k3_subset_1(sK2,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_239])).

cnf(c_670,plain,
    ( k3_subset_1(sK2,sK4) != X0
    | k3_subset_1(sK2,sK4) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_238])).

cnf(c_1732,plain,
    ( k3_subset_1(sK2,sK4) != k3_subset_1(sK2,k3_subset_1(sK2,sK3))
    | k3_subset_1(sK2,sK4) = sK3
    | sK3 != k3_subset_1(sK2,k3_subset_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_720,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_238])).

cnf(c_924,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_1163,plain,
    ( k3_subset_1(sK2,k3_subset_1(sK2,sK3)) != sK3
    | sK3 = k3_subset_1(sK2,k3_subset_1(sK2,sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_924])).

cnf(c_785,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_740,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_667,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | k3_subset_1(sK2,k3_subset_1(sK2,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_661,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | k4_xboole_0(sK2,sK3) = k3_subset_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_250,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_12,negated_conjecture,
    ( k3_subset_1(sK2,sK4) != sK3 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,negated_conjecture,
    ( r1_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_19,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_154954,c_147703,c_106826,c_37215,c_37214,c_14673,c_14669,c_12666,c_2079,c_1824,c_1732,c_1163,c_785,c_740,c_667,c_661,c_250,c_12,c_19,c_16])).


%------------------------------------------------------------------------------

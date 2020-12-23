%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:52 EST 2020

% Result     : Theorem 6.83s
% Output     : CNFRefutation 6.83s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 143 expanded)
%              Number of clauses        :   47 (  55 expanded)
%              Number of leaves         :   13 (  31 expanded)
%              Depth                    :   15
%              Number of atoms          :  341 ( 739 expanded)
%              Number of equality atoms :   69 (  97 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f29,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                   => r2_hidden(X3,X2) ) )
             => r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & ! [X3] :
              ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & ! [X3] :
              ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & ! [X3] :
              ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(X1,sK4)
        & ! [X3] :
            ( r2_hidden(X3,sK4)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X1,X2)
            & ! [X3] :
                ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(sK3,X2)
          & ! [X3] :
              ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,sK3)
              | ~ m1_subset_1(X3,sK2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r1_tarski(sK3,sK4)
    & ! [X3] :
        ( r2_hidden(X3,sK4)
        | ~ r2_hidden(X3,sK3)
        | ~ m1_subset_1(X3,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f27,f26])).

fof(f48,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK4)
      | ~ r2_hidden(X3,sK3)
      | ~ m1_subset_1(X3,sK2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & ~ r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(sK1(X0,X1,X2),X1)
          | r2_hidden(sK1(X0,X1,X2),X0)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & ~ r2_hidden(sK1(X0,X1,X2),X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( r2_hidden(sK1(X0,X1,X2),X1)
            | r2_hidden(sK1(X0,X1,X2),X0)
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f49,plain,(
    ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_14,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_117,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_1])).

cnf(c_118,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_117])).

cnf(c_18,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_254,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,sK4)
    | ~ r2_hidden(X2,sK3)
    | X2 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_118,c_18])).

cnf(c_255,plain,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_3444,plain,
    ( ~ r2_hidden(sK1(sK3,X0,sK4),sK2)
    | r2_hidden(sK1(sK3,X0,sK4),sK4)
    | ~ r2_hidden(sK1(sK3,X0,sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_36280,plain,
    ( ~ r2_hidden(sK1(sK3,sK4,sK4),sK2)
    | r2_hidden(sK1(sK3,sK4,sK4),sK4)
    | ~ r2_hidden(sK1(sK3,sK4,sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_3444])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_834,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_342,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_zfmisc_1(X2) != k1_zfmisc_1(sK2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_343,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK3)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK2) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_818,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK2)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_1088,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_818])).

cnf(c_2340,plain,
    ( k2_xboole_0(sK3,X0) = X1
    | r2_hidden(sK1(sK3,X0,X1),X1) = iProver_top
    | r2_hidden(sK1(sK3,X0,X1),X0) = iProver_top
    | r2_hidden(sK1(sK3,X0,X1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_834,c_1088])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_327,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_zfmisc_1(X2) != k1_zfmisc_1(sK2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_328,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK4)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK2) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_819,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK2)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_1118,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_819])).

cnf(c_15876,plain,
    ( k2_xboole_0(sK3,sK4) = X0
    | r2_hidden(sK1(sK3,sK4,X0),X0) = iProver_top
    | r2_hidden(sK1(sK3,sK4,X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2340,c_1118])).

cnf(c_17555,plain,
    ( k2_xboole_0(sK3,sK4) = sK4
    | r2_hidden(sK1(sK3,sK4,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_15876,c_1118])).

cnf(c_17610,plain,
    ( r2_hidden(sK1(sK3,sK4,sK4),sK2)
    | k2_xboole_0(sK3,sK4) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17555])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1038,plain,
    ( ~ r1_tarski(k2_xboole_0(sK3,X0),sK4)
    | r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_12389,plain,
    ( ~ r1_tarski(k2_xboole_0(sK3,sK4),sK4)
    | r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_429,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1097,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_xboole_0(sK3,X2),sK4)
    | k2_xboole_0(sK3,X2) != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_429])).

cnf(c_1175,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(k2_xboole_0(sK3,X1),sK4)
    | k2_xboole_0(sK3,X1) != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1097])).

cnf(c_1242,plain,
    ( r1_tarski(k2_xboole_0(sK3,X0),sK4)
    | ~ r1_tarski(sK4,sK4)
    | k2_xboole_0(sK3,X0) != sK4
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1175])).

cnf(c_3145,plain,
    ( r1_tarski(k2_xboole_0(sK3,sK4),sK4)
    | ~ r1_tarski(sK4,sK4)
    | k2_xboole_0(sK3,sK4) != sK4
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1242])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1185,plain,
    ( ~ r2_hidden(sK1(X0,X1,sK4),X1)
    | ~ r2_hidden(sK1(X0,X1,sK4),sK4)
    | k2_xboole_0(X0,X1) = sK4 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1378,plain,
    ( ~ r2_hidden(sK1(sK3,X0,sK4),X0)
    | ~ r2_hidden(sK1(sK3,X0,sK4),sK4)
    | k2_xboole_0(sK3,X0) = sK4 ),
    inference(instantiation,[status(thm)],[c_1185])).

cnf(c_1730,plain,
    ( ~ r2_hidden(sK1(sK3,sK4,sK4),sK4)
    | k2_xboole_0(sK3,sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_1183,plain,
    ( r2_hidden(sK1(X0,X1,sK4),X1)
    | r2_hidden(sK1(X0,X1,sK4),X0)
    | r2_hidden(sK1(X0,X1,sK4),sK4)
    | k2_xboole_0(X0,X1) = sK4 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1377,plain,
    ( r2_hidden(sK1(sK3,X0,sK4),X0)
    | r2_hidden(sK1(sK3,X0,sK4),sK4)
    | r2_hidden(sK1(sK3,X0,sK4),sK3)
    | k2_xboole_0(sK3,X0) = sK4 ),
    inference(instantiation,[status(thm)],[c_1183])).

cnf(c_1729,plain,
    ( r2_hidden(sK1(sK3,sK4,sK4),sK4)
    | r2_hidden(sK1(sK3,sK4,sK4),sK3)
    | k2_xboole_0(sK3,sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_1377])).

cnf(c_10,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1243,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_425,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1109,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_425])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_36280,c_17610,c_12389,c_3145,c_1730,c_1729,c_1243,c_1109,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:09:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 6.83/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.83/1.51  
% 6.83/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.83/1.51  
% 6.83/1.51  ------  iProver source info
% 6.83/1.51  
% 6.83/1.51  git: date: 2020-06-30 10:37:57 +0100
% 6.83/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.83/1.51  git: non_committed_changes: false
% 6.83/1.51  git: last_make_outside_of_git: false
% 6.83/1.51  
% 6.83/1.51  ------ 
% 6.83/1.51  
% 6.83/1.51  ------ Input Options
% 6.83/1.51  
% 6.83/1.51  --out_options                           all
% 6.83/1.51  --tptp_safe_out                         true
% 6.83/1.51  --problem_path                          ""
% 6.83/1.51  --include_path                          ""
% 6.83/1.51  --clausifier                            res/vclausify_rel
% 6.83/1.51  --clausifier_options                    --mode clausify
% 6.83/1.51  --stdin                                 false
% 6.83/1.51  --stats_out                             all
% 6.83/1.51  
% 6.83/1.51  ------ General Options
% 6.83/1.51  
% 6.83/1.51  --fof                                   false
% 6.83/1.51  --time_out_real                         305.
% 6.83/1.51  --time_out_virtual                      -1.
% 6.83/1.51  --symbol_type_check                     false
% 6.83/1.51  --clausify_out                          false
% 6.83/1.51  --sig_cnt_out                           false
% 6.83/1.51  --trig_cnt_out                          false
% 6.83/1.51  --trig_cnt_out_tolerance                1.
% 6.83/1.51  --trig_cnt_out_sk_spl                   false
% 6.83/1.51  --abstr_cl_out                          false
% 6.83/1.51  
% 6.83/1.51  ------ Global Options
% 6.83/1.51  
% 6.83/1.51  --schedule                              default
% 6.83/1.51  --add_important_lit                     false
% 6.83/1.51  --prop_solver_per_cl                    1000
% 6.83/1.51  --min_unsat_core                        false
% 6.83/1.51  --soft_assumptions                      false
% 6.83/1.51  --soft_lemma_size                       3
% 6.83/1.51  --prop_impl_unit_size                   0
% 6.83/1.51  --prop_impl_unit                        []
% 6.83/1.51  --share_sel_clauses                     true
% 6.83/1.51  --reset_solvers                         false
% 6.83/1.51  --bc_imp_inh                            [conj_cone]
% 6.83/1.51  --conj_cone_tolerance                   3.
% 6.83/1.51  --extra_neg_conj                        none
% 6.83/1.51  --large_theory_mode                     true
% 6.83/1.51  --prolific_symb_bound                   200
% 6.83/1.51  --lt_threshold                          2000
% 6.83/1.51  --clause_weak_htbl                      true
% 6.83/1.51  --gc_record_bc_elim                     false
% 6.83/1.51  
% 6.83/1.51  ------ Preprocessing Options
% 6.83/1.51  
% 6.83/1.51  --preprocessing_flag                    true
% 6.83/1.51  --time_out_prep_mult                    0.1
% 6.83/1.51  --splitting_mode                        input
% 6.83/1.51  --splitting_grd                         true
% 6.83/1.51  --splitting_cvd                         false
% 6.83/1.51  --splitting_cvd_svl                     false
% 6.83/1.51  --splitting_nvd                         32
% 6.83/1.51  --sub_typing                            true
% 6.83/1.51  --prep_gs_sim                           true
% 6.83/1.51  --prep_unflatten                        true
% 6.83/1.51  --prep_res_sim                          true
% 6.83/1.51  --prep_upred                            true
% 6.83/1.51  --prep_sem_filter                       exhaustive
% 6.83/1.51  --prep_sem_filter_out                   false
% 6.83/1.51  --pred_elim                             true
% 6.83/1.51  --res_sim_input                         true
% 6.83/1.51  --eq_ax_congr_red                       true
% 6.83/1.51  --pure_diseq_elim                       true
% 6.83/1.51  --brand_transform                       false
% 6.83/1.51  --non_eq_to_eq                          false
% 6.83/1.51  --prep_def_merge                        true
% 6.83/1.51  --prep_def_merge_prop_impl              false
% 6.83/1.51  --prep_def_merge_mbd                    true
% 6.83/1.51  --prep_def_merge_tr_red                 false
% 6.83/1.51  --prep_def_merge_tr_cl                  false
% 6.83/1.51  --smt_preprocessing                     true
% 6.83/1.51  --smt_ac_axioms                         fast
% 6.83/1.51  --preprocessed_out                      false
% 6.83/1.51  --preprocessed_stats                    false
% 6.83/1.51  
% 6.83/1.51  ------ Abstraction refinement Options
% 6.83/1.51  
% 6.83/1.51  --abstr_ref                             []
% 6.83/1.51  --abstr_ref_prep                        false
% 6.83/1.51  --abstr_ref_until_sat                   false
% 6.83/1.51  --abstr_ref_sig_restrict                funpre
% 6.83/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 6.83/1.51  --abstr_ref_under                       []
% 6.83/1.51  
% 6.83/1.51  ------ SAT Options
% 6.83/1.51  
% 6.83/1.51  --sat_mode                              false
% 6.83/1.51  --sat_fm_restart_options                ""
% 6.83/1.51  --sat_gr_def                            false
% 6.83/1.51  --sat_epr_types                         true
% 6.83/1.51  --sat_non_cyclic_types                  false
% 6.83/1.51  --sat_finite_models                     false
% 6.83/1.51  --sat_fm_lemmas                         false
% 6.83/1.51  --sat_fm_prep                           false
% 6.83/1.51  --sat_fm_uc_incr                        true
% 6.83/1.51  --sat_out_model                         small
% 6.83/1.51  --sat_out_clauses                       false
% 6.83/1.51  
% 6.83/1.51  ------ QBF Options
% 6.83/1.51  
% 6.83/1.51  --qbf_mode                              false
% 6.83/1.51  --qbf_elim_univ                         false
% 6.83/1.51  --qbf_dom_inst                          none
% 6.83/1.51  --qbf_dom_pre_inst                      false
% 6.83/1.51  --qbf_sk_in                             false
% 6.83/1.51  --qbf_pred_elim                         true
% 6.83/1.51  --qbf_split                             512
% 6.83/1.51  
% 6.83/1.51  ------ BMC1 Options
% 6.83/1.51  
% 6.83/1.51  --bmc1_incremental                      false
% 6.83/1.51  --bmc1_axioms                           reachable_all
% 6.83/1.51  --bmc1_min_bound                        0
% 6.83/1.51  --bmc1_max_bound                        -1
% 6.83/1.51  --bmc1_max_bound_default                -1
% 6.83/1.51  --bmc1_symbol_reachability              true
% 6.83/1.51  --bmc1_property_lemmas                  false
% 6.83/1.51  --bmc1_k_induction                      false
% 6.83/1.51  --bmc1_non_equiv_states                 false
% 6.83/1.51  --bmc1_deadlock                         false
% 6.83/1.51  --bmc1_ucm                              false
% 6.83/1.51  --bmc1_add_unsat_core                   none
% 6.83/1.51  --bmc1_unsat_core_children              false
% 6.83/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 6.83/1.51  --bmc1_out_stat                         full
% 6.83/1.51  --bmc1_ground_init                      false
% 6.83/1.51  --bmc1_pre_inst_next_state              false
% 6.83/1.51  --bmc1_pre_inst_state                   false
% 6.83/1.51  --bmc1_pre_inst_reach_state             false
% 6.83/1.51  --bmc1_out_unsat_core                   false
% 6.83/1.51  --bmc1_aig_witness_out                  false
% 6.83/1.51  --bmc1_verbose                          false
% 6.83/1.51  --bmc1_dump_clauses_tptp                false
% 6.83/1.51  --bmc1_dump_unsat_core_tptp             false
% 6.83/1.51  --bmc1_dump_file                        -
% 6.83/1.51  --bmc1_ucm_expand_uc_limit              128
% 6.83/1.51  --bmc1_ucm_n_expand_iterations          6
% 6.83/1.51  --bmc1_ucm_extend_mode                  1
% 6.83/1.51  --bmc1_ucm_init_mode                    2
% 6.83/1.51  --bmc1_ucm_cone_mode                    none
% 6.83/1.51  --bmc1_ucm_reduced_relation_type        0
% 6.83/1.51  --bmc1_ucm_relax_model                  4
% 6.83/1.51  --bmc1_ucm_full_tr_after_sat            true
% 6.83/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 6.83/1.51  --bmc1_ucm_layered_model                none
% 6.83/1.51  --bmc1_ucm_max_lemma_size               10
% 6.83/1.51  
% 6.83/1.51  ------ AIG Options
% 6.83/1.51  
% 6.83/1.51  --aig_mode                              false
% 6.83/1.51  
% 6.83/1.51  ------ Instantiation Options
% 6.83/1.51  
% 6.83/1.51  --instantiation_flag                    true
% 6.83/1.51  --inst_sos_flag                         false
% 6.83/1.51  --inst_sos_phase                        true
% 6.83/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.83/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.83/1.51  --inst_lit_sel_side                     num_symb
% 6.83/1.51  --inst_solver_per_active                1400
% 6.83/1.51  --inst_solver_calls_frac                1.
% 6.83/1.51  --inst_passive_queue_type               priority_queues
% 6.83/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.83/1.51  --inst_passive_queues_freq              [25;2]
% 6.83/1.51  --inst_dismatching                      true
% 6.83/1.51  --inst_eager_unprocessed_to_passive     true
% 6.83/1.51  --inst_prop_sim_given                   true
% 6.83/1.51  --inst_prop_sim_new                     false
% 6.83/1.51  --inst_subs_new                         false
% 6.83/1.51  --inst_eq_res_simp                      false
% 6.83/1.51  --inst_subs_given                       false
% 6.83/1.51  --inst_orphan_elimination               true
% 6.83/1.51  --inst_learning_loop_flag               true
% 6.83/1.51  --inst_learning_start                   3000
% 6.83/1.51  --inst_learning_factor                  2
% 6.83/1.51  --inst_start_prop_sim_after_learn       3
% 6.83/1.51  --inst_sel_renew                        solver
% 6.83/1.51  --inst_lit_activity_flag                true
% 6.83/1.51  --inst_restr_to_given                   false
% 6.83/1.51  --inst_activity_threshold               500
% 6.83/1.51  --inst_out_proof                        true
% 6.83/1.51  
% 6.83/1.51  ------ Resolution Options
% 6.83/1.51  
% 6.83/1.51  --resolution_flag                       true
% 6.83/1.51  --res_lit_sel                           adaptive
% 6.83/1.51  --res_lit_sel_side                      none
% 6.83/1.51  --res_ordering                          kbo
% 6.83/1.51  --res_to_prop_solver                    active
% 6.83/1.51  --res_prop_simpl_new                    false
% 6.83/1.51  --res_prop_simpl_given                  true
% 6.83/1.51  --res_passive_queue_type                priority_queues
% 6.83/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.83/1.51  --res_passive_queues_freq               [15;5]
% 6.83/1.51  --res_forward_subs                      full
% 6.83/1.51  --res_backward_subs                     full
% 6.83/1.51  --res_forward_subs_resolution           true
% 6.83/1.51  --res_backward_subs_resolution          true
% 6.83/1.51  --res_orphan_elimination                true
% 6.83/1.51  --res_time_limit                        2.
% 6.83/1.51  --res_out_proof                         true
% 6.83/1.51  
% 6.83/1.51  ------ Superposition Options
% 6.83/1.51  
% 6.83/1.51  --superposition_flag                    true
% 6.83/1.51  --sup_passive_queue_type                priority_queues
% 6.83/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.83/1.51  --sup_passive_queues_freq               [8;1;4]
% 6.83/1.51  --demod_completeness_check              fast
% 6.83/1.51  --demod_use_ground                      true
% 6.83/1.51  --sup_to_prop_solver                    passive
% 6.83/1.51  --sup_prop_simpl_new                    true
% 6.83/1.51  --sup_prop_simpl_given                  true
% 6.83/1.51  --sup_fun_splitting                     false
% 6.83/1.51  --sup_smt_interval                      50000
% 6.83/1.51  
% 6.83/1.51  ------ Superposition Simplification Setup
% 6.83/1.51  
% 6.83/1.51  --sup_indices_passive                   []
% 6.83/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.83/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.83/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.83/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 6.83/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.83/1.51  --sup_full_bw                           [BwDemod]
% 6.83/1.51  --sup_immed_triv                        [TrivRules]
% 6.83/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.83/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.83/1.51  --sup_immed_bw_main                     []
% 6.83/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.83/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 6.83/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.83/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.83/1.51  
% 6.83/1.51  ------ Combination Options
% 6.83/1.51  
% 6.83/1.51  --comb_res_mult                         3
% 6.83/1.51  --comb_sup_mult                         2
% 6.83/1.51  --comb_inst_mult                        10
% 6.83/1.51  
% 6.83/1.51  ------ Debug Options
% 6.83/1.51  
% 6.83/1.51  --dbg_backtrace                         false
% 6.83/1.51  --dbg_dump_prop_clauses                 false
% 6.83/1.51  --dbg_dump_prop_clauses_file            -
% 6.83/1.51  --dbg_out_stat                          false
% 6.83/1.51  ------ Parsing...
% 6.83/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.83/1.51  
% 6.83/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 6.83/1.51  
% 6.83/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.83/1.51  
% 6.83/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.83/1.51  ------ Proving...
% 6.83/1.51  ------ Problem Properties 
% 6.83/1.51  
% 6.83/1.51  
% 6.83/1.51  clauses                                 23
% 6.83/1.51  conjectures                             1
% 6.83/1.51  EPR                                     6
% 6.83/1.51  Horn                                    18
% 6.83/1.51  unary                                   2
% 6.83/1.51  binary                                  9
% 6.83/1.51  lits                                    58
% 6.83/1.51  lits eq                                 8
% 6.83/1.51  fd_pure                                 0
% 6.83/1.51  fd_pseudo                               0
% 6.83/1.51  fd_cond                                 0
% 6.83/1.51  fd_pseudo_cond                          4
% 6.83/1.51  AC symbols                              0
% 6.83/1.51  
% 6.83/1.51  ------ Schedule dynamic 5 is on 
% 6.83/1.51  
% 6.83/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.83/1.51  
% 6.83/1.51  
% 6.83/1.51  ------ 
% 6.83/1.51  Current options:
% 6.83/1.51  ------ 
% 6.83/1.51  
% 6.83/1.51  ------ Input Options
% 6.83/1.51  
% 6.83/1.51  --out_options                           all
% 6.83/1.51  --tptp_safe_out                         true
% 6.83/1.51  --problem_path                          ""
% 6.83/1.51  --include_path                          ""
% 6.83/1.51  --clausifier                            res/vclausify_rel
% 6.83/1.51  --clausifier_options                    --mode clausify
% 6.83/1.51  --stdin                                 false
% 6.83/1.51  --stats_out                             all
% 6.83/1.51  
% 6.83/1.51  ------ General Options
% 6.83/1.51  
% 6.83/1.51  --fof                                   false
% 6.83/1.51  --time_out_real                         305.
% 6.83/1.51  --time_out_virtual                      -1.
% 6.83/1.51  --symbol_type_check                     false
% 6.83/1.51  --clausify_out                          false
% 6.83/1.51  --sig_cnt_out                           false
% 6.83/1.51  --trig_cnt_out                          false
% 6.83/1.51  --trig_cnt_out_tolerance                1.
% 6.83/1.51  --trig_cnt_out_sk_spl                   false
% 6.83/1.51  --abstr_cl_out                          false
% 6.83/1.51  
% 6.83/1.51  ------ Global Options
% 6.83/1.51  
% 6.83/1.51  --schedule                              default
% 6.83/1.51  --add_important_lit                     false
% 6.83/1.51  --prop_solver_per_cl                    1000
% 6.83/1.51  --min_unsat_core                        false
% 6.83/1.51  --soft_assumptions                      false
% 6.83/1.51  --soft_lemma_size                       3
% 6.83/1.51  --prop_impl_unit_size                   0
% 6.83/1.51  --prop_impl_unit                        []
% 6.83/1.51  --share_sel_clauses                     true
% 6.83/1.51  --reset_solvers                         false
% 6.83/1.51  --bc_imp_inh                            [conj_cone]
% 6.83/1.51  --conj_cone_tolerance                   3.
% 6.83/1.51  --extra_neg_conj                        none
% 6.83/1.51  --large_theory_mode                     true
% 6.83/1.51  --prolific_symb_bound                   200
% 6.83/1.51  --lt_threshold                          2000
% 6.83/1.51  --clause_weak_htbl                      true
% 6.83/1.51  --gc_record_bc_elim                     false
% 6.83/1.51  
% 6.83/1.51  ------ Preprocessing Options
% 6.83/1.51  
% 6.83/1.51  --preprocessing_flag                    true
% 6.83/1.51  --time_out_prep_mult                    0.1
% 6.83/1.51  --splitting_mode                        input
% 6.83/1.51  --splitting_grd                         true
% 6.83/1.51  --splitting_cvd                         false
% 6.83/1.51  --splitting_cvd_svl                     false
% 6.83/1.51  --splitting_nvd                         32
% 6.83/1.51  --sub_typing                            true
% 6.83/1.51  --prep_gs_sim                           true
% 6.83/1.51  --prep_unflatten                        true
% 6.83/1.51  --prep_res_sim                          true
% 6.83/1.51  --prep_upred                            true
% 6.83/1.51  --prep_sem_filter                       exhaustive
% 6.83/1.51  --prep_sem_filter_out                   false
% 6.83/1.51  --pred_elim                             true
% 6.83/1.51  --res_sim_input                         true
% 6.83/1.51  --eq_ax_congr_red                       true
% 6.83/1.51  --pure_diseq_elim                       true
% 6.83/1.51  --brand_transform                       false
% 6.83/1.51  --non_eq_to_eq                          false
% 6.83/1.51  --prep_def_merge                        true
% 6.83/1.51  --prep_def_merge_prop_impl              false
% 6.83/1.51  --prep_def_merge_mbd                    true
% 6.83/1.51  --prep_def_merge_tr_red                 false
% 6.83/1.51  --prep_def_merge_tr_cl                  false
% 6.83/1.51  --smt_preprocessing                     true
% 6.83/1.51  --smt_ac_axioms                         fast
% 6.83/1.51  --preprocessed_out                      false
% 6.83/1.51  --preprocessed_stats                    false
% 6.83/1.51  
% 6.83/1.51  ------ Abstraction refinement Options
% 6.83/1.51  
% 6.83/1.51  --abstr_ref                             []
% 6.83/1.51  --abstr_ref_prep                        false
% 6.83/1.51  --abstr_ref_until_sat                   false
% 6.83/1.51  --abstr_ref_sig_restrict                funpre
% 6.83/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 6.83/1.51  --abstr_ref_under                       []
% 6.83/1.51  
% 6.83/1.51  ------ SAT Options
% 6.83/1.51  
% 6.83/1.51  --sat_mode                              false
% 6.83/1.51  --sat_fm_restart_options                ""
% 6.83/1.51  --sat_gr_def                            false
% 6.83/1.51  --sat_epr_types                         true
% 6.83/1.51  --sat_non_cyclic_types                  false
% 6.83/1.51  --sat_finite_models                     false
% 6.83/1.51  --sat_fm_lemmas                         false
% 6.83/1.51  --sat_fm_prep                           false
% 6.83/1.51  --sat_fm_uc_incr                        true
% 6.83/1.51  --sat_out_model                         small
% 6.83/1.51  --sat_out_clauses                       false
% 6.83/1.51  
% 6.83/1.51  ------ QBF Options
% 6.83/1.51  
% 6.83/1.51  --qbf_mode                              false
% 6.83/1.51  --qbf_elim_univ                         false
% 6.83/1.51  --qbf_dom_inst                          none
% 6.83/1.51  --qbf_dom_pre_inst                      false
% 6.83/1.51  --qbf_sk_in                             false
% 6.83/1.51  --qbf_pred_elim                         true
% 6.83/1.51  --qbf_split                             512
% 6.83/1.51  
% 6.83/1.51  ------ BMC1 Options
% 6.83/1.51  
% 6.83/1.51  --bmc1_incremental                      false
% 6.83/1.51  --bmc1_axioms                           reachable_all
% 6.83/1.51  --bmc1_min_bound                        0
% 6.83/1.51  --bmc1_max_bound                        -1
% 6.83/1.51  --bmc1_max_bound_default                -1
% 6.83/1.51  --bmc1_symbol_reachability              true
% 6.83/1.52  --bmc1_property_lemmas                  false
% 6.83/1.52  --bmc1_k_induction                      false
% 6.83/1.52  --bmc1_non_equiv_states                 false
% 6.83/1.52  --bmc1_deadlock                         false
% 6.83/1.52  --bmc1_ucm                              false
% 6.83/1.52  --bmc1_add_unsat_core                   none
% 6.83/1.52  --bmc1_unsat_core_children              false
% 6.83/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 6.83/1.52  --bmc1_out_stat                         full
% 6.83/1.52  --bmc1_ground_init                      false
% 6.83/1.52  --bmc1_pre_inst_next_state              false
% 6.83/1.52  --bmc1_pre_inst_state                   false
% 6.83/1.52  --bmc1_pre_inst_reach_state             false
% 6.83/1.52  --bmc1_out_unsat_core                   false
% 6.83/1.52  --bmc1_aig_witness_out                  false
% 6.83/1.52  --bmc1_verbose                          false
% 6.83/1.52  --bmc1_dump_clauses_tptp                false
% 6.83/1.52  --bmc1_dump_unsat_core_tptp             false
% 6.83/1.52  --bmc1_dump_file                        -
% 6.83/1.52  --bmc1_ucm_expand_uc_limit              128
% 6.83/1.52  --bmc1_ucm_n_expand_iterations          6
% 6.83/1.52  --bmc1_ucm_extend_mode                  1
% 6.83/1.52  --bmc1_ucm_init_mode                    2
% 6.83/1.52  --bmc1_ucm_cone_mode                    none
% 6.83/1.52  --bmc1_ucm_reduced_relation_type        0
% 6.83/1.52  --bmc1_ucm_relax_model                  4
% 6.83/1.52  --bmc1_ucm_full_tr_after_sat            true
% 6.83/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 6.83/1.52  --bmc1_ucm_layered_model                none
% 6.83/1.52  --bmc1_ucm_max_lemma_size               10
% 6.83/1.52  
% 6.83/1.52  ------ AIG Options
% 6.83/1.52  
% 6.83/1.52  --aig_mode                              false
% 6.83/1.52  
% 6.83/1.52  ------ Instantiation Options
% 6.83/1.52  
% 6.83/1.52  --instantiation_flag                    true
% 6.83/1.52  --inst_sos_flag                         false
% 6.83/1.52  --inst_sos_phase                        true
% 6.83/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.83/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.83/1.52  --inst_lit_sel_side                     none
% 6.83/1.52  --inst_solver_per_active                1400
% 6.83/1.52  --inst_solver_calls_frac                1.
% 6.83/1.52  --inst_passive_queue_type               priority_queues
% 6.83/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.83/1.52  --inst_passive_queues_freq              [25;2]
% 6.83/1.52  --inst_dismatching                      true
% 6.83/1.52  --inst_eager_unprocessed_to_passive     true
% 6.83/1.52  --inst_prop_sim_given                   true
% 6.83/1.52  --inst_prop_sim_new                     false
% 6.83/1.52  --inst_subs_new                         false
% 6.83/1.52  --inst_eq_res_simp                      false
% 6.83/1.52  --inst_subs_given                       false
% 6.83/1.52  --inst_orphan_elimination               true
% 6.83/1.52  --inst_learning_loop_flag               true
% 6.83/1.52  --inst_learning_start                   3000
% 6.83/1.52  --inst_learning_factor                  2
% 6.83/1.52  --inst_start_prop_sim_after_learn       3
% 6.83/1.52  --inst_sel_renew                        solver
% 6.83/1.52  --inst_lit_activity_flag                true
% 6.83/1.52  --inst_restr_to_given                   false
% 6.83/1.52  --inst_activity_threshold               500
% 6.83/1.52  --inst_out_proof                        true
% 6.83/1.52  
% 6.83/1.52  ------ Resolution Options
% 6.83/1.52  
% 6.83/1.52  --resolution_flag                       false
% 6.83/1.52  --res_lit_sel                           adaptive
% 6.83/1.52  --res_lit_sel_side                      none
% 6.83/1.52  --res_ordering                          kbo
% 6.83/1.52  --res_to_prop_solver                    active
% 6.83/1.52  --res_prop_simpl_new                    false
% 6.83/1.52  --res_prop_simpl_given                  true
% 6.83/1.52  --res_passive_queue_type                priority_queues
% 6.83/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.83/1.52  --res_passive_queues_freq               [15;5]
% 6.83/1.52  --res_forward_subs                      full
% 6.83/1.52  --res_backward_subs                     full
% 6.83/1.52  --res_forward_subs_resolution           true
% 6.83/1.52  --res_backward_subs_resolution          true
% 6.83/1.52  --res_orphan_elimination                true
% 6.83/1.52  --res_time_limit                        2.
% 6.83/1.52  --res_out_proof                         true
% 6.83/1.52  
% 6.83/1.52  ------ Superposition Options
% 6.83/1.52  
% 6.83/1.52  --superposition_flag                    true
% 6.83/1.52  --sup_passive_queue_type                priority_queues
% 6.83/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.83/1.52  --sup_passive_queues_freq               [8;1;4]
% 6.83/1.52  --demod_completeness_check              fast
% 6.83/1.52  --demod_use_ground                      true
% 6.83/1.52  --sup_to_prop_solver                    passive
% 6.83/1.52  --sup_prop_simpl_new                    true
% 6.83/1.52  --sup_prop_simpl_given                  true
% 6.83/1.52  --sup_fun_splitting                     false
% 6.83/1.52  --sup_smt_interval                      50000
% 6.83/1.52  
% 6.83/1.52  ------ Superposition Simplification Setup
% 6.83/1.52  
% 6.83/1.52  --sup_indices_passive                   []
% 6.83/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.83/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.83/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.83/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 6.83/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.83/1.52  --sup_full_bw                           [BwDemod]
% 6.83/1.52  --sup_immed_triv                        [TrivRules]
% 6.83/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.83/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.83/1.52  --sup_immed_bw_main                     []
% 6.83/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.83/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 6.83/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.83/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.83/1.52  
% 6.83/1.52  ------ Combination Options
% 6.83/1.52  
% 6.83/1.52  --comb_res_mult                         3
% 6.83/1.52  --comb_sup_mult                         2
% 6.83/1.52  --comb_inst_mult                        10
% 6.83/1.52  
% 6.83/1.52  ------ Debug Options
% 6.83/1.52  
% 6.83/1.52  --dbg_backtrace                         false
% 6.83/1.52  --dbg_dump_prop_clauses                 false
% 6.83/1.52  --dbg_dump_prop_clauses_file            -
% 6.83/1.52  --dbg_out_stat                          false
% 6.83/1.52  
% 6.83/1.52  
% 6.83/1.52  
% 6.83/1.52  
% 6.83/1.52  ------ Proving...
% 6.83/1.52  
% 6.83/1.52  
% 6.83/1.52  % SZS status Theorem for theBenchmark.p
% 6.83/1.52  
% 6.83/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 6.83/1.52  
% 6.83/1.52  fof(f5,axiom,(
% 6.83/1.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 6.83/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.83/1.52  
% 6.83/1.52  fof(f10,plain,(
% 6.83/1.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 6.83/1.52    inference(ennf_transformation,[],[f5])).
% 6.83/1.52  
% 6.83/1.52  fof(f25,plain,(
% 6.83/1.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 6.83/1.52    inference(nnf_transformation,[],[f10])).
% 6.83/1.52  
% 6.83/1.52  fof(f42,plain,(
% 6.83/1.52    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 6.83/1.52    inference(cnf_transformation,[],[f25])).
% 6.83/1.52  
% 6.83/1.52  fof(f1,axiom,(
% 6.83/1.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 6.83/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.83/1.52  
% 6.83/1.52  fof(f14,plain,(
% 6.83/1.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 6.83/1.52    inference(nnf_transformation,[],[f1])).
% 6.83/1.52  
% 6.83/1.52  fof(f15,plain,(
% 6.83/1.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 6.83/1.52    inference(rectify,[],[f14])).
% 6.83/1.52  
% 6.83/1.52  fof(f16,plain,(
% 6.83/1.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 6.83/1.52    introduced(choice_axiom,[])).
% 6.83/1.52  
% 6.83/1.52  fof(f17,plain,(
% 6.83/1.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 6.83/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 6.83/1.52  
% 6.83/1.52  fof(f29,plain,(
% 6.83/1.52    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 6.83/1.52    inference(cnf_transformation,[],[f17])).
% 6.83/1.52  
% 6.83/1.52  fof(f7,conjecture,(
% 6.83/1.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 6.83/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.83/1.52  
% 6.83/1.52  fof(f8,negated_conjecture,(
% 6.83/1.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 6.83/1.52    inference(negated_conjecture,[],[f7])).
% 6.83/1.52  
% 6.83/1.52  fof(f12,plain,(
% 6.83/1.52    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) & ! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.83/1.52    inference(ennf_transformation,[],[f8])).
% 6.83/1.52  
% 6.83/1.52  fof(f13,plain,(
% 6.83/1.52    ? [X0,X1] : (? [X2] : (~r1_tarski(X1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.83/1.52    inference(flattening,[],[f12])).
% 6.83/1.52  
% 6.83/1.52  fof(f27,plain,(
% 6.83/1.52    ( ! [X0,X1] : (? [X2] : (~r1_tarski(X1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (~r1_tarski(X1,sK4) & ! [X3] : (r2_hidden(X3,sK4) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,X0)) & m1_subset_1(sK4,k1_zfmisc_1(X0)))) )),
% 6.83/1.52    introduced(choice_axiom,[])).
% 6.83/1.52  
% 6.83/1.52  fof(f26,plain,(
% 6.83/1.52    ? [X0,X1] : (? [X2] : (~r1_tarski(X1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(sK3,X2) & ! [X3] : (r2_hidden(X3,X2) | ~r2_hidden(X3,sK3) | ~m1_subset_1(X3,sK2)) & m1_subset_1(X2,k1_zfmisc_1(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(sK2)))),
% 6.83/1.52    introduced(choice_axiom,[])).
% 6.83/1.52  
% 6.83/1.52  fof(f28,plain,(
% 6.83/1.52    (~r1_tarski(sK3,sK4) & ! [X3] : (r2_hidden(X3,sK4) | ~r2_hidden(X3,sK3) | ~m1_subset_1(X3,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 6.83/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f27,f26])).
% 6.83/1.52  
% 6.83/1.52  fof(f48,plain,(
% 6.83/1.52    ( ! [X3] : (r2_hidden(X3,sK4) | ~r2_hidden(X3,sK3) | ~m1_subset_1(X3,sK2)) )),
% 6.83/1.52    inference(cnf_transformation,[],[f28])).
% 6.83/1.52  
% 6.83/1.52  fof(f2,axiom,(
% 6.83/1.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 6.83/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.83/1.52  
% 6.83/1.52  fof(f18,plain,(
% 6.83/1.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.83/1.52    inference(nnf_transformation,[],[f2])).
% 6.83/1.52  
% 6.83/1.52  fof(f19,plain,(
% 6.83/1.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.83/1.52    inference(flattening,[],[f18])).
% 6.83/1.52  
% 6.83/1.52  fof(f20,plain,(
% 6.83/1.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.83/1.52    inference(rectify,[],[f19])).
% 6.83/1.52  
% 6.83/1.52  fof(f21,plain,(
% 6.83/1.52    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 6.83/1.52    introduced(choice_axiom,[])).
% 6.83/1.52  
% 6.83/1.52  fof(f22,plain,(
% 6.83/1.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.83/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).
% 6.83/1.52  
% 6.83/1.52  fof(f34,plain,(
% 6.83/1.52    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 6.83/1.52    inference(cnf_transformation,[],[f22])).
% 6.83/1.52  
% 6.83/1.52  fof(f6,axiom,(
% 6.83/1.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 6.83/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.83/1.52  
% 6.83/1.52  fof(f11,plain,(
% 6.83/1.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.83/1.52    inference(ennf_transformation,[],[f6])).
% 6.83/1.52  
% 6.83/1.52  fof(f45,plain,(
% 6.83/1.52    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.83/1.52    inference(cnf_transformation,[],[f11])).
% 6.83/1.52  
% 6.83/1.52  fof(f46,plain,(
% 6.83/1.52    m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 6.83/1.52    inference(cnf_transformation,[],[f28])).
% 6.83/1.52  
% 6.83/1.52  fof(f47,plain,(
% 6.83/1.52    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 6.83/1.52    inference(cnf_transformation,[],[f28])).
% 6.83/1.52  
% 6.83/1.52  fof(f4,axiom,(
% 6.83/1.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 6.83/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.83/1.52  
% 6.83/1.52  fof(f9,plain,(
% 6.83/1.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 6.83/1.52    inference(ennf_transformation,[],[f4])).
% 6.83/1.52  
% 6.83/1.52  fof(f40,plain,(
% 6.83/1.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 6.83/1.52    inference(cnf_transformation,[],[f9])).
% 6.83/1.52  
% 6.83/1.52  fof(f36,plain,(
% 6.83/1.52    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 6.83/1.52    inference(cnf_transformation,[],[f22])).
% 6.83/1.52  
% 6.83/1.52  fof(f3,axiom,(
% 6.83/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.83/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.83/1.52  
% 6.83/1.52  fof(f23,plain,(
% 6.83/1.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.83/1.52    inference(nnf_transformation,[],[f3])).
% 6.83/1.52  
% 6.83/1.52  fof(f24,plain,(
% 6.83/1.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.83/1.52    inference(flattening,[],[f23])).
% 6.83/1.52  
% 6.83/1.52  fof(f37,plain,(
% 6.83/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.83/1.52    inference(cnf_transformation,[],[f24])).
% 6.83/1.52  
% 6.83/1.52  fof(f54,plain,(
% 6.83/1.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.83/1.52    inference(equality_resolution,[],[f37])).
% 6.83/1.52  
% 6.83/1.52  fof(f49,plain,(
% 6.83/1.52    ~r1_tarski(sK3,sK4)),
% 6.83/1.52    inference(cnf_transformation,[],[f28])).
% 6.83/1.52  
% 6.83/1.52  cnf(c_14,plain,
% 6.83/1.52      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 6.83/1.52      inference(cnf_transformation,[],[f42]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_1,plain,
% 6.83/1.52      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 6.83/1.52      inference(cnf_transformation,[],[f29]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_117,plain,
% 6.83/1.52      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 6.83/1.52      inference(global_propositional_subsumption,
% 6.83/1.52                [status(thm)],
% 6.83/1.52                [c_14,c_1]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_118,plain,
% 6.83/1.52      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 6.83/1.52      inference(renaming,[status(thm)],[c_117]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_18,negated_conjecture,
% 6.83/1.52      ( ~ m1_subset_1(X0,sK2) | r2_hidden(X0,sK4) | ~ r2_hidden(X0,sK3) ),
% 6.83/1.52      inference(cnf_transformation,[],[f48]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_254,plain,
% 6.83/1.52      ( ~ r2_hidden(X0,X1)
% 6.83/1.52      | r2_hidden(X2,sK4)
% 6.83/1.52      | ~ r2_hidden(X2,sK3)
% 6.83/1.52      | X2 != X0
% 6.83/1.52      | sK2 != X1 ),
% 6.83/1.52      inference(resolution_lifted,[status(thm)],[c_118,c_18]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_255,plain,
% 6.83/1.52      ( ~ r2_hidden(X0,sK2) | r2_hidden(X0,sK4) | ~ r2_hidden(X0,sK3) ),
% 6.83/1.52      inference(unflattening,[status(thm)],[c_254]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_3444,plain,
% 6.83/1.52      ( ~ r2_hidden(sK1(sK3,X0,sK4),sK2)
% 6.83/1.52      | r2_hidden(sK1(sK3,X0,sK4),sK4)
% 6.83/1.52      | ~ r2_hidden(sK1(sK3,X0,sK4),sK3) ),
% 6.83/1.52      inference(instantiation,[status(thm)],[c_255]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_36280,plain,
% 6.83/1.52      ( ~ r2_hidden(sK1(sK3,sK4,sK4),sK2)
% 6.83/1.52      | r2_hidden(sK1(sK3,sK4,sK4),sK4)
% 6.83/1.52      | ~ r2_hidden(sK1(sK3,sK4,sK4),sK3) ),
% 6.83/1.52      inference(instantiation,[status(thm)],[c_3444]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_4,plain,
% 6.83/1.52      ( r2_hidden(sK1(X0,X1,X2),X1)
% 6.83/1.52      | r2_hidden(sK1(X0,X1,X2),X2)
% 6.83/1.52      | r2_hidden(sK1(X0,X1,X2),X0)
% 6.83/1.52      | k2_xboole_0(X0,X1) = X2 ),
% 6.83/1.52      inference(cnf_transformation,[],[f34]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_834,plain,
% 6.83/1.52      ( k2_xboole_0(X0,X1) = X2
% 6.83/1.52      | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top
% 6.83/1.52      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
% 6.83/1.52      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top ),
% 6.83/1.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_16,plain,
% 6.83/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.83/1.52      | ~ r2_hidden(X2,X0)
% 6.83/1.52      | r2_hidden(X2,X1) ),
% 6.83/1.52      inference(cnf_transformation,[],[f45]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_20,negated_conjecture,
% 6.83/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
% 6.83/1.52      inference(cnf_transformation,[],[f46]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_342,plain,
% 6.83/1.52      ( ~ r2_hidden(X0,X1)
% 6.83/1.52      | r2_hidden(X0,X2)
% 6.83/1.52      | k1_zfmisc_1(X2) != k1_zfmisc_1(sK2)
% 6.83/1.52      | sK3 != X1 ),
% 6.83/1.52      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_343,plain,
% 6.83/1.52      ( r2_hidden(X0,X1)
% 6.83/1.52      | ~ r2_hidden(X0,sK3)
% 6.83/1.52      | k1_zfmisc_1(X1) != k1_zfmisc_1(sK2) ),
% 6.83/1.52      inference(unflattening,[status(thm)],[c_342]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_818,plain,
% 6.83/1.52      ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK2)
% 6.83/1.52      | r2_hidden(X1,X0) = iProver_top
% 6.83/1.52      | r2_hidden(X1,sK3) != iProver_top ),
% 6.83/1.52      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_1088,plain,
% 6.83/1.52      ( r2_hidden(X0,sK2) = iProver_top
% 6.83/1.52      | r2_hidden(X0,sK3) != iProver_top ),
% 6.83/1.52      inference(equality_resolution,[status(thm)],[c_818]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_2340,plain,
% 6.83/1.52      ( k2_xboole_0(sK3,X0) = X1
% 6.83/1.52      | r2_hidden(sK1(sK3,X0,X1),X1) = iProver_top
% 6.83/1.52      | r2_hidden(sK1(sK3,X0,X1),X0) = iProver_top
% 6.83/1.52      | r2_hidden(sK1(sK3,X0,X1),sK2) = iProver_top ),
% 6.83/1.52      inference(superposition,[status(thm)],[c_834,c_1088]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_19,negated_conjecture,
% 6.83/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 6.83/1.52      inference(cnf_transformation,[],[f47]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_327,plain,
% 6.83/1.52      ( ~ r2_hidden(X0,X1)
% 6.83/1.52      | r2_hidden(X0,X2)
% 6.83/1.52      | k1_zfmisc_1(X2) != k1_zfmisc_1(sK2)
% 6.83/1.52      | sK4 != X1 ),
% 6.83/1.52      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_328,plain,
% 6.83/1.52      ( r2_hidden(X0,X1)
% 6.83/1.52      | ~ r2_hidden(X0,sK4)
% 6.83/1.52      | k1_zfmisc_1(X1) != k1_zfmisc_1(sK2) ),
% 6.83/1.52      inference(unflattening,[status(thm)],[c_327]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_819,plain,
% 6.83/1.52      ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK2)
% 6.83/1.52      | r2_hidden(X1,X0) = iProver_top
% 6.83/1.52      | r2_hidden(X1,sK4) != iProver_top ),
% 6.83/1.52      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_1118,plain,
% 6.83/1.52      ( r2_hidden(X0,sK2) = iProver_top
% 6.83/1.52      | r2_hidden(X0,sK4) != iProver_top ),
% 6.83/1.52      inference(equality_resolution,[status(thm)],[c_819]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_15876,plain,
% 6.83/1.52      ( k2_xboole_0(sK3,sK4) = X0
% 6.83/1.52      | r2_hidden(sK1(sK3,sK4,X0),X0) = iProver_top
% 6.83/1.52      | r2_hidden(sK1(sK3,sK4,X0),sK2) = iProver_top ),
% 6.83/1.52      inference(superposition,[status(thm)],[c_2340,c_1118]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_17555,plain,
% 6.83/1.52      ( k2_xboole_0(sK3,sK4) = sK4
% 6.83/1.52      | r2_hidden(sK1(sK3,sK4,sK4),sK2) = iProver_top ),
% 6.83/1.52      inference(superposition,[status(thm)],[c_15876,c_1118]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_17610,plain,
% 6.83/1.52      ( r2_hidden(sK1(sK3,sK4,sK4),sK2) | k2_xboole_0(sK3,sK4) = sK4 ),
% 6.83/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_17555]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_11,plain,
% 6.83/1.52      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 6.83/1.52      inference(cnf_transformation,[],[f40]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_1038,plain,
% 6.83/1.52      ( ~ r1_tarski(k2_xboole_0(sK3,X0),sK4) | r1_tarski(sK3,sK4) ),
% 6.83/1.52      inference(instantiation,[status(thm)],[c_11]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_12389,plain,
% 6.83/1.52      ( ~ r1_tarski(k2_xboole_0(sK3,sK4),sK4) | r1_tarski(sK3,sK4) ),
% 6.83/1.52      inference(instantiation,[status(thm)],[c_1038]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_429,plain,
% 6.83/1.52      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.83/1.52      theory(equality) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_1097,plain,
% 6.83/1.52      ( ~ r1_tarski(X0,X1)
% 6.83/1.52      | r1_tarski(k2_xboole_0(sK3,X2),sK4)
% 6.83/1.52      | k2_xboole_0(sK3,X2) != X0
% 6.83/1.52      | sK4 != X1 ),
% 6.83/1.52      inference(instantiation,[status(thm)],[c_429]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_1175,plain,
% 6.83/1.52      ( ~ r1_tarski(X0,sK4)
% 6.83/1.52      | r1_tarski(k2_xboole_0(sK3,X1),sK4)
% 6.83/1.52      | k2_xboole_0(sK3,X1) != X0
% 6.83/1.52      | sK4 != sK4 ),
% 6.83/1.52      inference(instantiation,[status(thm)],[c_1097]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_1242,plain,
% 6.83/1.52      ( r1_tarski(k2_xboole_0(sK3,X0),sK4)
% 6.83/1.52      | ~ r1_tarski(sK4,sK4)
% 6.83/1.52      | k2_xboole_0(sK3,X0) != sK4
% 6.83/1.52      | sK4 != sK4 ),
% 6.83/1.52      inference(instantiation,[status(thm)],[c_1175]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_3145,plain,
% 6.83/1.52      ( r1_tarski(k2_xboole_0(sK3,sK4),sK4)
% 6.83/1.52      | ~ r1_tarski(sK4,sK4)
% 6.83/1.52      | k2_xboole_0(sK3,sK4) != sK4
% 6.83/1.52      | sK4 != sK4 ),
% 6.83/1.52      inference(instantiation,[status(thm)],[c_1242]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_2,plain,
% 6.83/1.52      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 6.83/1.52      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 6.83/1.52      | k2_xboole_0(X0,X1) = X2 ),
% 6.83/1.52      inference(cnf_transformation,[],[f36]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_1185,plain,
% 6.83/1.52      ( ~ r2_hidden(sK1(X0,X1,sK4),X1)
% 6.83/1.52      | ~ r2_hidden(sK1(X0,X1,sK4),sK4)
% 6.83/1.52      | k2_xboole_0(X0,X1) = sK4 ),
% 6.83/1.52      inference(instantiation,[status(thm)],[c_2]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_1378,plain,
% 6.83/1.52      ( ~ r2_hidden(sK1(sK3,X0,sK4),X0)
% 6.83/1.52      | ~ r2_hidden(sK1(sK3,X0,sK4),sK4)
% 6.83/1.52      | k2_xboole_0(sK3,X0) = sK4 ),
% 6.83/1.52      inference(instantiation,[status(thm)],[c_1185]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_1730,plain,
% 6.83/1.52      ( ~ r2_hidden(sK1(sK3,sK4,sK4),sK4) | k2_xboole_0(sK3,sK4) = sK4 ),
% 6.83/1.52      inference(instantiation,[status(thm)],[c_1378]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_1183,plain,
% 6.83/1.52      ( r2_hidden(sK1(X0,X1,sK4),X1)
% 6.83/1.52      | r2_hidden(sK1(X0,X1,sK4),X0)
% 6.83/1.52      | r2_hidden(sK1(X0,X1,sK4),sK4)
% 6.83/1.52      | k2_xboole_0(X0,X1) = sK4 ),
% 6.83/1.52      inference(instantiation,[status(thm)],[c_4]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_1377,plain,
% 6.83/1.52      ( r2_hidden(sK1(sK3,X0,sK4),X0)
% 6.83/1.52      | r2_hidden(sK1(sK3,X0,sK4),sK4)
% 6.83/1.52      | r2_hidden(sK1(sK3,X0,sK4),sK3)
% 6.83/1.52      | k2_xboole_0(sK3,X0) = sK4 ),
% 6.83/1.52      inference(instantiation,[status(thm)],[c_1183]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_1729,plain,
% 6.83/1.52      ( r2_hidden(sK1(sK3,sK4,sK4),sK4)
% 6.83/1.52      | r2_hidden(sK1(sK3,sK4,sK4),sK3)
% 6.83/1.52      | k2_xboole_0(sK3,sK4) = sK4 ),
% 6.83/1.52      inference(instantiation,[status(thm)],[c_1377]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_10,plain,
% 6.83/1.52      ( r1_tarski(X0,X0) ),
% 6.83/1.52      inference(cnf_transformation,[],[f54]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_1243,plain,
% 6.83/1.52      ( r1_tarski(sK4,sK4) ),
% 6.83/1.52      inference(instantiation,[status(thm)],[c_10]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_425,plain,( X0 = X0 ),theory(equality) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_1109,plain,
% 6.83/1.52      ( sK4 = sK4 ),
% 6.83/1.52      inference(instantiation,[status(thm)],[c_425]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(c_17,negated_conjecture,
% 6.83/1.52      ( ~ r1_tarski(sK3,sK4) ),
% 6.83/1.52      inference(cnf_transformation,[],[f49]) ).
% 6.83/1.52  
% 6.83/1.52  cnf(contradiction,plain,
% 6.83/1.52      ( $false ),
% 6.83/1.52      inference(minisat,
% 6.83/1.52                [status(thm)],
% 6.83/1.52                [c_36280,c_17610,c_12389,c_3145,c_1730,c_1729,c_1243,
% 6.83/1.52                 c_1109,c_17]) ).
% 6.83/1.52  
% 6.83/1.52  
% 6.83/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 6.83/1.52  
% 6.83/1.52  ------                               Statistics
% 6.83/1.52  
% 6.83/1.52  ------ General
% 6.83/1.52  
% 6.83/1.52  abstr_ref_over_cycles:                  0
% 6.83/1.52  abstr_ref_under_cycles:                 0
% 6.83/1.52  gc_basic_clause_elim:                   0
% 6.83/1.52  forced_gc_time:                         0
% 6.83/1.52  parsing_time:                           0.016
% 6.83/1.52  unif_index_cands_time:                  0.
% 6.83/1.52  unif_index_add_time:                    0.
% 6.83/1.52  orderings_time:                         0.
% 6.83/1.52  out_proof_time:                         0.009
% 6.83/1.52  total_time:                             0.752
% 6.83/1.52  num_of_symbols:                         42
% 6.83/1.52  num_of_terms:                           35000
% 6.83/1.52  
% 6.83/1.52  ------ Preprocessing
% 6.83/1.52  
% 6.83/1.52  num_of_splits:                          0
% 6.83/1.52  num_of_split_atoms:                     0
% 6.83/1.52  num_of_reused_defs:                     0
% 6.83/1.52  num_eq_ax_congr_red:                    13
% 6.83/1.52  num_of_sem_filtered_clauses:            1
% 6.83/1.52  num_of_subtypes:                        0
% 6.83/1.52  monotx_restored_types:                  0
% 6.83/1.52  sat_num_of_epr_types:                   0
% 6.83/1.52  sat_num_of_non_cyclic_types:            0
% 6.83/1.52  sat_guarded_non_collapsed_types:        0
% 6.83/1.52  num_pure_diseq_elim:                    0
% 6.83/1.52  simp_replaced_by:                       0
% 6.83/1.52  res_preprocessed:                       79
% 6.83/1.52  prep_upred:                             0
% 6.83/1.52  prep_unflattend:                        20
% 6.83/1.52  smt_new_axioms:                         0
% 6.83/1.52  pred_elim_cands:                        4
% 6.83/1.52  pred_elim:                              1
% 6.83/1.52  pred_elim_cl:                           -3
% 6.83/1.52  pred_elim_cycles:                       2
% 6.83/1.52  merged_defs:                            0
% 6.83/1.52  merged_defs_ncl:                        0
% 6.83/1.52  bin_hyper_res:                          0
% 6.83/1.52  prep_cycles:                            3
% 6.83/1.52  pred_elim_time:                         0.002
% 6.83/1.52  splitting_time:                         0.
% 6.83/1.52  sem_filter_time:                        0.
% 6.83/1.52  monotx_time:                            0.
% 6.83/1.52  subtype_inf_time:                       0.
% 6.83/1.52  
% 6.83/1.52  ------ Problem properties
% 6.83/1.52  
% 6.83/1.52  clauses:                                23
% 6.83/1.52  conjectures:                            1
% 6.83/1.52  epr:                                    6
% 6.83/1.52  horn:                                   18
% 6.83/1.52  ground:                                 7
% 6.83/1.52  unary:                                  2
% 6.83/1.52  binary:                                 9
% 6.83/1.52  lits:                                   58
% 6.83/1.52  lits_eq:                                8
% 6.83/1.52  fd_pure:                                0
% 6.83/1.52  fd_pseudo:                              0
% 6.83/1.52  fd_cond:                                0
% 6.83/1.52  fd_pseudo_cond:                         4
% 6.83/1.52  ac_symbols:                             0
% 6.83/1.52  
% 6.83/1.52  ------ Propositional Solver
% 6.83/1.52  
% 6.83/1.52  prop_solver_calls:                      30
% 6.83/1.52  prop_fast_solver_calls:                 1112
% 6.83/1.52  smt_solver_calls:                       0
% 6.83/1.52  smt_fast_solver_calls:                  0
% 6.83/1.52  prop_num_of_clauses:                    10037
% 6.83/1.52  prop_preprocess_simplified:             14202
% 6.83/1.52  prop_fo_subsumed:                       34
% 6.83/1.52  prop_solver_time:                       0.
% 6.83/1.52  smt_solver_time:                        0.
% 6.83/1.52  smt_fast_solver_time:                   0.
% 6.83/1.52  prop_fast_solver_time:                  0.
% 6.83/1.52  prop_unsat_core_time:                   0.
% 6.83/1.52  
% 6.83/1.52  ------ QBF
% 6.83/1.52  
% 6.83/1.52  qbf_q_res:                              0
% 6.83/1.52  qbf_num_tautologies:                    0
% 6.83/1.52  qbf_prep_cycles:                        0
% 6.83/1.52  
% 6.83/1.52  ------ BMC1
% 6.83/1.52  
% 6.83/1.52  bmc1_current_bound:                     -1
% 6.83/1.52  bmc1_last_solved_bound:                 -1
% 6.83/1.52  bmc1_unsat_core_size:                   -1
% 6.83/1.52  bmc1_unsat_core_parents_size:           -1
% 6.83/1.52  bmc1_merge_next_fun:                    0
% 6.83/1.52  bmc1_unsat_core_clauses_time:           0.
% 6.83/1.52  
% 6.83/1.52  ------ Instantiation
% 6.83/1.52  
% 6.83/1.52  inst_num_of_clauses:                    2051
% 6.83/1.52  inst_num_in_passive:                    226
% 6.83/1.52  inst_num_in_active:                     827
% 6.83/1.52  inst_num_in_unprocessed:                997
% 6.83/1.52  inst_num_of_loops:                      1064
% 6.83/1.52  inst_num_of_learning_restarts:          0
% 6.83/1.52  inst_num_moves_active_passive:          229
% 6.83/1.52  inst_lit_activity:                      0
% 6.83/1.52  inst_lit_activity_moves:                0
% 6.83/1.52  inst_num_tautologies:                   0
% 6.83/1.52  inst_num_prop_implied:                  0
% 6.83/1.52  inst_num_existing_simplified:           0
% 6.83/1.52  inst_num_eq_res_simplified:             0
% 6.83/1.52  inst_num_child_elim:                    0
% 6.83/1.52  inst_num_of_dismatching_blockings:      3449
% 6.83/1.52  inst_num_of_non_proper_insts:           2417
% 6.83/1.52  inst_num_of_duplicates:                 0
% 6.83/1.52  inst_inst_num_from_inst_to_res:         0
% 6.83/1.52  inst_dismatching_checking_time:         0.
% 6.83/1.52  
% 6.83/1.52  ------ Resolution
% 6.83/1.52  
% 6.83/1.52  res_num_of_clauses:                     0
% 6.83/1.52  res_num_in_passive:                     0
% 6.83/1.52  res_num_in_active:                      0
% 6.83/1.52  res_num_of_loops:                       82
% 6.83/1.52  res_forward_subset_subsumed:            112
% 6.83/1.52  res_backward_subset_subsumed:           2
% 6.83/1.52  res_forward_subsumed:                   1
% 6.83/1.52  res_backward_subsumed:                  0
% 6.83/1.52  res_forward_subsumption_resolution:     0
% 6.83/1.52  res_backward_subsumption_resolution:    0
% 6.83/1.52  res_clause_to_clause_subsumption:       10601
% 6.83/1.52  res_orphan_elimination:                 0
% 6.83/1.52  res_tautology_del:                      529
% 6.83/1.52  res_num_eq_res_simplified:              0
% 6.83/1.52  res_num_sel_changes:                    0
% 6.83/1.52  res_moves_from_active_to_pass:          0
% 6.83/1.52  
% 6.83/1.52  ------ Superposition
% 6.83/1.52  
% 6.83/1.52  sup_time_total:                         0.
% 6.83/1.52  sup_time_generating:                    0.
% 6.83/1.52  sup_time_sim_full:                      0.
% 6.83/1.52  sup_time_sim_immed:                     0.
% 6.83/1.52  
% 6.83/1.52  sup_num_of_clauses:                     1014
% 6.83/1.52  sup_num_in_active:                      195
% 6.83/1.52  sup_num_in_passive:                     819
% 6.83/1.52  sup_num_of_loops:                       212
% 6.83/1.52  sup_fw_superposition:                   294
% 6.83/1.52  sup_bw_superposition:                   1495
% 6.83/1.52  sup_immediate_simplified:               534
% 6.83/1.52  sup_given_eliminated:                   0
% 6.83/1.52  comparisons_done:                       0
% 6.83/1.52  comparisons_avoided:                    0
% 6.83/1.52  
% 6.83/1.52  ------ Simplifications
% 6.83/1.52  
% 6.83/1.52  
% 6.83/1.52  sim_fw_subset_subsumed:                 345
% 6.83/1.52  sim_bw_subset_subsumed:                 20
% 6.83/1.52  sim_fw_subsumed:                        209
% 6.83/1.52  sim_bw_subsumed:                        0
% 6.83/1.52  sim_fw_subsumption_res:                 16
% 6.83/1.52  sim_bw_subsumption_res:                 1
% 6.83/1.52  sim_tautology_del:                      63
% 6.83/1.52  sim_eq_tautology_del:                   30
% 6.83/1.52  sim_eq_res_simp:                        215
% 6.83/1.52  sim_fw_demodulated:                     7
% 6.83/1.52  sim_bw_demodulated:                     5
% 6.83/1.52  sim_light_normalised:                   63
% 6.83/1.52  sim_joinable_taut:                      0
% 6.83/1.52  sim_joinable_simp:                      0
% 6.83/1.52  sim_ac_normalised:                      0
% 6.83/1.52  sim_smt_subsumption:                    0
% 6.83/1.52  
%------------------------------------------------------------------------------

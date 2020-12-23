%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:03 EST 2020

% Result     : Theorem 54.97s
% Output     : CNFRefutation 54.97s
% Verified   : 
% Statistics : Number of formulae       :  147 (5151 expanded)
%              Number of clauses        :   97 (1597 expanded)
%              Number of leaves         :   11 (1128 expanded)
%              Depth                    :   30
%              Number of atoms          :  488 (27627 expanded)
%              Number of equality atoms :  206 (5439 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f28,plain,(
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
               => ( ~ r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( ~ r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ~ r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ~ r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( k3_subset_1(X0,sK4) != X1
        & ! [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X3,sK4) )
              & ( r2_hidden(X3,sK4)
                | r2_hidden(X3,X1) ) )
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & ! [X3] :
                ( ( ( ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k3_subset_1(sK2,X2) != sK3
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,sK3)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,sK3) ) )
              | ~ m1_subset_1(X3,sK2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( k3_subset_1(sK2,sK4) != sK3
    & ! [X3] :
        ( ( ( ~ r2_hidden(X3,sK3)
            | ~ r2_hidden(X3,sK4) )
          & ( r2_hidden(X3,sK4)
            | r2_hidden(X3,sK3) ) )
        | ~ m1_subset_1(X3,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f26,f25])).

fof(f45,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK4)
      | r2_hidden(X3,sK3)
      | ~ m1_subset_1(X3,sK2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f41,f36])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f46,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK3)
      | ~ r2_hidden(X3,sK4)
      | ~ m1_subset_1(X3,sK2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f52])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f47,plain,(
    k3_subset_1(sK2,sK4) != sK3 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_832,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_103,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_1])).

cnf(c_104,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_103])).

cnf(c_819,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_104])).

cnf(c_2977,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | m1_subset_1(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_832,c_819])).

cnf(c_16,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | r2_hidden(X0,sK3)
    | r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_822,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_24170,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) = X1
    | r2_hidden(sK1(sK2,X0,X1),X1) = iProver_top
    | r2_hidden(sK1(sK2,X0,X1),sK3) = iProver_top
    | r2_hidden(sK1(sK2,X0,X1),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2977,c_822])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_833,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_24847,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = X0
    | r2_hidden(sK1(sK2,sK3,X0),X0) = iProver_top
    | r2_hidden(sK1(sK2,sK3,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_24170,c_833])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_820,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_825,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1566,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = k3_subset_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_820,c_825])).

cnf(c_24991,plain,
    ( k3_subset_1(sK2,sK3) = X0
    | r2_hidden(sK1(sK2,sK3,X0),X0) = iProver_top
    | r2_hidden(sK1(sK2,sK3,X0),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_24847,c_1566])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_821,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_824,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1250,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_821,c_824])).

cnf(c_25226,plain,
    ( k3_subset_1(sK2,sK3) = X0
    | r2_hidden(sK1(sK2,sK3,X0),X0) = iProver_top
    | r2_hidden(sK1(sK2,sK3,X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_24991,c_1250])).

cnf(c_25390,plain,
    ( k3_subset_1(sK2,sK3) = sK4
    | r2_hidden(sK1(sK2,sK3,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_25226,c_1250])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_834,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_26000,plain,
    ( k3_subset_1(sK2,sK3) = sK4
    | k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = sK4
    | r2_hidden(sK1(sK2,sK3,sK4),sK3) = iProver_top
    | r2_hidden(sK1(sK2,sK3,sK4),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_25390,c_834])).

cnf(c_26005,plain,
    ( k3_subset_1(sK2,sK3) = sK4
    | r2_hidden(sK1(sK2,sK3,sK4),sK3) = iProver_top
    | r2_hidden(sK1(sK2,sK3,sK4),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_26000,c_1566])).

cnf(c_25245,plain,
    ( k3_subset_1(sK2,sK3) = sK4
    | r2_hidden(sK1(sK2,sK3,sK4),sK4) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_24991])).

cnf(c_25247,plain,
    ( k3_subset_1(sK2,sK3) = sK4
    | r2_hidden(sK1(sK2,sK3,sK4),sK4) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_25245])).

cnf(c_27300,plain,
    ( r2_hidden(sK1(sK2,sK3,sK4),sK3) = iProver_top
    | k3_subset_1(sK2,sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_26005,c_25247])).

cnf(c_27301,plain,
    ( k3_subset_1(sK2,sK3) = sK4
    | r2_hidden(sK1(sK2,sK3,sK4),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_27300])).

cnf(c_1251,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_820,c_824])).

cnf(c_2974,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = sK3
    | r2_hidden(sK1(X0,X1,sK3),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_832,c_1251])).

cnf(c_6993,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
    | r2_hidden(sK1(sK3,X0,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2974,c_1251])).

cnf(c_7086,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
    | m1_subset_1(sK1(sK3,X0,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6993,c_819])).

cnf(c_17292,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
    | r2_hidden(sK1(sK3,X0,sK3),sK3) = iProver_top
    | r2_hidden(sK1(sK3,X0,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7086,c_822])).

cnf(c_1987,plain,
    ( r2_hidden(sK1(sK3,X0,X1),X1)
    | r2_hidden(sK1(sK3,X0,X1),sK3)
    | k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = X1 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2713,plain,
    ( r2_hidden(sK1(sK3,X0,sK3),sK3)
    | k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3 ),
    inference(instantiation,[status(thm)],[c_1987])).

cnf(c_2715,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
    | r2_hidden(sK1(sK3,X0,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2713])).

cnf(c_19331,plain,
    ( r2_hidden(sK1(sK3,X0,sK3),sK3) = iProver_top
    | k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17292,c_2715])).

cnf(c_19332,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
    | r2_hidden(sK1(sK3,X0,sK3),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_19331])).

cnf(c_19339,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
    | r2_hidden(sK1(sK3,X0,sK3),X0) = iProver_top
    | r2_hidden(sK1(sK3,X0,sK3),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_19332,c_834])).

cnf(c_19346,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
    | r2_hidden(sK1(sK3,X0,sK3),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19339,c_19332])).

cnf(c_15,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_823,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17293,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
    | r2_hidden(sK1(sK3,X0,sK3),sK3) != iProver_top
    | r2_hidden(sK1(sK3,X0,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7086,c_823])).

cnf(c_19,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1451,plain,
    ( ~ m1_subset_1(sK1(X0,X1,sK3),sK2)
    | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
    | ~ r2_hidden(sK1(X0,X1,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_5323,plain,
    ( ~ m1_subset_1(sK1(sK3,X0,sK3),sK2)
    | ~ r2_hidden(sK1(sK3,X0,sK3),sK3)
    | ~ r2_hidden(sK1(sK3,X0,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1451])).

cnf(c_5326,plain,
    ( m1_subset_1(sK1(sK3,X0,sK3),sK2) != iProver_top
    | r2_hidden(sK1(sK3,X0,sK3),sK3) != iProver_top
    | r2_hidden(sK1(sK3,X0,sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5323])).

cnf(c_2683,plain,
    ( m1_subset_1(sK1(sK3,X0,X1),sK2)
    | ~ r2_hidden(sK1(sK3,X0,X1),sK2) ),
    inference(instantiation,[status(thm)],[c_104])).

cnf(c_7859,plain,
    ( m1_subset_1(sK1(sK3,X0,sK3),sK2)
    | ~ r2_hidden(sK1(sK3,X0,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_2683])).

cnf(c_7863,plain,
    ( m1_subset_1(sK1(sK3,X0,sK3),sK2) = iProver_top
    | r2_hidden(sK1(sK3,X0,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7859])).

cnf(c_3125,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK1(X1,X2,sK3),X0)
    | r2_hidden(sK1(X1,X2,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_8974,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
    | r2_hidden(sK1(X0,X1,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_3125])).

cnf(c_15967,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK1(sK3,X0,sK3),sK3)
    | r2_hidden(sK1(sK3,X0,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_8974])).

cnf(c_15971,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK3,X0,sK3),sK3) != iProver_top
    | r2_hidden(sK1(sK3,X0,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15967])).

cnf(c_17311,plain,
    ( r2_hidden(sK1(sK3,X0,sK3),sK3) != iProver_top
    | r2_hidden(sK1(sK3,X0,sK3),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17293,c_19,c_5326,c_7863,c_15971])).

cnf(c_17322,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
    | r2_hidden(sK1(sK3,X0,sK3),sK3) = iProver_top
    | r2_hidden(sK1(sK3,X0,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_832,c_17311])).

cnf(c_17340,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
    | r2_hidden(sK1(sK3,X0,sK3),sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17322,c_17311])).

cnf(c_21971,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) = sK3 ),
    inference(superposition,[status(thm)],[c_19346,c_17340])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_830,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_69764,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_21971,c_830])).

cnf(c_72696,plain,
    ( k3_subset_1(sK2,sK3) = sK4
    | r2_hidden(sK1(sK2,sK3,sK4),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_27301,c_69764])).

cnf(c_80629,plain,
    ( k3_subset_1(sK2,sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_72696,c_25247])).

cnf(c_80692,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = sK4 ),
    inference(demodulation,[status(thm)],[c_80629,c_1566])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_831,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3090,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X3
    | r2_hidden(sK1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X1) != iProver_top
    | r2_hidden(sK1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X3) = iProver_top
    | r2_hidden(sK1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_831,c_833])).

cnf(c_32888,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X2
    | r2_hidden(sK1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X2) = iProver_top
    | r2_hidden(sK1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_832,c_3090])).

cnf(c_231331,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)))) = X0
    | r2_hidden(sK1(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)),X0),sK3) = iProver_top
    | r2_hidden(sK1(sK2,sK4,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_80692,c_32888])).

cnf(c_1565,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) = k3_subset_1(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_821,c_825])).

cnf(c_232184,plain,
    ( k3_subset_1(sK2,sK4) = X0
    | r2_hidden(sK1(sK2,sK4,X0),X0) = iProver_top
    | r2_hidden(sK1(sK2,sK4,X0),sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_231331,c_1565,c_80692])).

cnf(c_233708,plain,
    ( k3_subset_1(sK2,sK4) = X0
    | r2_hidden(sK1(sK2,sK4,X0),X0) = iProver_top
    | r2_hidden(sK1(sK2,sK4,X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_232184,c_1251])).

cnf(c_234063,plain,
    ( k3_subset_1(sK2,sK4) = sK3
    | r2_hidden(sK1(sK2,sK4,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_233708,c_1251])).

cnf(c_14,negated_conjecture,
    ( k3_subset_1(sK2,sK4) != sK3 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_156033,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK1(X0,sK4,sK3),sK3)
    | r2_hidden(sK1(X0,sK4,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_8974])).

cnf(c_156034,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(X0,sK4,sK3),sK3) != iProver_top
    | r2_hidden(sK1(X0,sK4,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_156033])).

cnf(c_156036,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,sK4,sK3),sK3) != iProver_top
    | r2_hidden(sK1(sK2,sK4,sK3),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_156034])).

cnf(c_233754,plain,
    ( k3_subset_1(sK2,sK4) = sK3
    | r2_hidden(sK1(sK2,sK4,sK3),sK3) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_232184])).

cnf(c_233756,plain,
    ( k3_subset_1(sK2,sK4) = sK3
    | r2_hidden(sK1(sK2,sK4,sK3),sK3) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_233754])).

cnf(c_234518,plain,
    ( r2_hidden(sK1(sK2,sK4,sK3),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_234063,c_19,c_14,c_156036,c_233756])).

cnf(c_234525,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) = sK3
    | r2_hidden(sK1(sK2,sK4,sK3),sK3) != iProver_top
    | r2_hidden(sK1(sK2,sK4,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_234518,c_834])).

cnf(c_234534,plain,
    ( k3_subset_1(sK2,sK4) = sK3
    | r2_hidden(sK1(sK2,sK4,sK3),sK3) != iProver_top
    | r2_hidden(sK1(sK2,sK4,sK3),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_234525,c_1565])).

cnf(c_12079,plain,
    ( ~ m1_subset_1(sK1(X0,sK4,sK3),sK2)
    | ~ r2_hidden(sK1(X0,sK4,sK3),sK3)
    | ~ r2_hidden(sK1(X0,sK4,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1451])).

cnf(c_12084,plain,
    ( m1_subset_1(sK1(X0,sK4,sK3),sK2) != iProver_top
    | r2_hidden(sK1(X0,sK4,sK3),sK3) != iProver_top
    | r2_hidden(sK1(X0,sK4,sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12079])).

cnf(c_12086,plain,
    ( m1_subset_1(sK1(sK2,sK4,sK3),sK2) != iProver_top
    | r2_hidden(sK1(sK2,sK4,sK3),sK3) != iProver_top
    | r2_hidden(sK1(sK2,sK4,sK3),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12084])).

cnf(c_1587,plain,
    ( m1_subset_1(sK1(X0,X1,sK3),sK2)
    | ~ r2_hidden(sK1(X0,X1,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_104])).

cnf(c_11595,plain,
    ( m1_subset_1(sK1(X0,sK4,sK3),sK2)
    | ~ r2_hidden(sK1(X0,sK4,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_11596,plain,
    ( m1_subset_1(sK1(X0,sK4,sK3),sK2) = iProver_top
    | r2_hidden(sK1(X0,sK4,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11595])).

cnf(c_11598,plain,
    ( m1_subset_1(sK1(sK2,sK4,sK3),sK2) = iProver_top
    | r2_hidden(sK1(sK2,sK4,sK3),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11596])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_234534,c_233756,c_156036,c_12086,c_11598,c_14,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 54.97/7.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 54.97/7.52  
% 54.97/7.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 54.97/7.52  
% 54.97/7.52  ------  iProver source info
% 54.97/7.52  
% 54.97/7.52  git: date: 2020-06-30 10:37:57 +0100
% 54.97/7.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 54.97/7.52  git: non_committed_changes: false
% 54.97/7.52  git: last_make_outside_of_git: false
% 54.97/7.52  
% 54.97/7.52  ------ 
% 54.97/7.52  
% 54.97/7.52  ------ Input Options
% 54.97/7.52  
% 54.97/7.52  --out_options                           all
% 54.97/7.52  --tptp_safe_out                         true
% 54.97/7.52  --problem_path                          ""
% 54.97/7.52  --include_path                          ""
% 54.97/7.52  --clausifier                            res/vclausify_rel
% 54.97/7.52  --clausifier_options                    --mode clausify
% 54.97/7.52  --stdin                                 false
% 54.97/7.52  --stats_out                             all
% 54.97/7.52  
% 54.97/7.52  ------ General Options
% 54.97/7.52  
% 54.97/7.52  --fof                                   false
% 54.97/7.52  --time_out_real                         305.
% 54.97/7.52  --time_out_virtual                      -1.
% 54.97/7.52  --symbol_type_check                     false
% 54.97/7.52  --clausify_out                          false
% 54.97/7.52  --sig_cnt_out                           false
% 54.97/7.52  --trig_cnt_out                          false
% 54.97/7.52  --trig_cnt_out_tolerance                1.
% 54.97/7.52  --trig_cnt_out_sk_spl                   false
% 54.97/7.52  --abstr_cl_out                          false
% 54.97/7.52  
% 54.97/7.52  ------ Global Options
% 54.97/7.52  
% 54.97/7.52  --schedule                              default
% 54.97/7.52  --add_important_lit                     false
% 54.97/7.52  --prop_solver_per_cl                    1000
% 54.97/7.52  --min_unsat_core                        false
% 54.97/7.52  --soft_assumptions                      false
% 54.97/7.52  --soft_lemma_size                       3
% 54.97/7.52  --prop_impl_unit_size                   0
% 54.97/7.52  --prop_impl_unit                        []
% 54.97/7.52  --share_sel_clauses                     true
% 54.97/7.52  --reset_solvers                         false
% 54.97/7.52  --bc_imp_inh                            [conj_cone]
% 54.97/7.52  --conj_cone_tolerance                   3.
% 54.97/7.52  --extra_neg_conj                        none
% 54.97/7.52  --large_theory_mode                     true
% 54.97/7.52  --prolific_symb_bound                   200
% 54.97/7.52  --lt_threshold                          2000
% 54.97/7.52  --clause_weak_htbl                      true
% 54.97/7.52  --gc_record_bc_elim                     false
% 54.97/7.52  
% 54.97/7.52  ------ Preprocessing Options
% 54.97/7.52  
% 54.97/7.52  --preprocessing_flag                    true
% 54.97/7.52  --time_out_prep_mult                    0.1
% 54.97/7.52  --splitting_mode                        input
% 54.97/7.52  --splitting_grd                         true
% 54.97/7.52  --splitting_cvd                         false
% 54.97/7.52  --splitting_cvd_svl                     false
% 54.97/7.52  --splitting_nvd                         32
% 54.97/7.52  --sub_typing                            true
% 54.97/7.52  --prep_gs_sim                           true
% 54.97/7.52  --prep_unflatten                        true
% 54.97/7.52  --prep_res_sim                          true
% 54.97/7.52  --prep_upred                            true
% 54.97/7.52  --prep_sem_filter                       exhaustive
% 54.97/7.52  --prep_sem_filter_out                   false
% 54.97/7.52  --pred_elim                             true
% 54.97/7.52  --res_sim_input                         true
% 54.97/7.52  --eq_ax_congr_red                       true
% 54.97/7.52  --pure_diseq_elim                       true
% 54.97/7.52  --brand_transform                       false
% 54.97/7.52  --non_eq_to_eq                          false
% 54.97/7.52  --prep_def_merge                        true
% 54.97/7.52  --prep_def_merge_prop_impl              false
% 54.97/7.52  --prep_def_merge_mbd                    true
% 54.97/7.52  --prep_def_merge_tr_red                 false
% 54.97/7.52  --prep_def_merge_tr_cl                  false
% 54.97/7.52  --smt_preprocessing                     true
% 54.97/7.52  --smt_ac_axioms                         fast
% 54.97/7.52  --preprocessed_out                      false
% 54.97/7.52  --preprocessed_stats                    false
% 54.97/7.52  
% 54.97/7.52  ------ Abstraction refinement Options
% 54.97/7.52  
% 54.97/7.52  --abstr_ref                             []
% 54.97/7.52  --abstr_ref_prep                        false
% 54.97/7.52  --abstr_ref_until_sat                   false
% 54.97/7.52  --abstr_ref_sig_restrict                funpre
% 54.97/7.52  --abstr_ref_af_restrict_to_split_sk     false
% 54.97/7.52  --abstr_ref_under                       []
% 54.97/7.52  
% 54.97/7.52  ------ SAT Options
% 54.97/7.52  
% 54.97/7.52  --sat_mode                              false
% 54.97/7.52  --sat_fm_restart_options                ""
% 54.97/7.52  --sat_gr_def                            false
% 54.97/7.52  --sat_epr_types                         true
% 54.97/7.52  --sat_non_cyclic_types                  false
% 54.97/7.52  --sat_finite_models                     false
% 54.97/7.52  --sat_fm_lemmas                         false
% 54.97/7.52  --sat_fm_prep                           false
% 54.97/7.52  --sat_fm_uc_incr                        true
% 54.97/7.52  --sat_out_model                         small
% 54.97/7.52  --sat_out_clauses                       false
% 54.97/7.52  
% 54.97/7.52  ------ QBF Options
% 54.97/7.52  
% 54.97/7.52  --qbf_mode                              false
% 54.97/7.52  --qbf_elim_univ                         false
% 54.97/7.52  --qbf_dom_inst                          none
% 54.97/7.52  --qbf_dom_pre_inst                      false
% 54.97/7.52  --qbf_sk_in                             false
% 54.97/7.52  --qbf_pred_elim                         true
% 54.97/7.52  --qbf_split                             512
% 54.97/7.52  
% 54.97/7.52  ------ BMC1 Options
% 54.97/7.52  
% 54.97/7.52  --bmc1_incremental                      false
% 54.97/7.52  --bmc1_axioms                           reachable_all
% 54.97/7.52  --bmc1_min_bound                        0
% 54.97/7.52  --bmc1_max_bound                        -1
% 54.97/7.52  --bmc1_max_bound_default                -1
% 54.97/7.52  --bmc1_symbol_reachability              true
% 54.97/7.52  --bmc1_property_lemmas                  false
% 54.97/7.52  --bmc1_k_induction                      false
% 54.97/7.52  --bmc1_non_equiv_states                 false
% 54.97/7.52  --bmc1_deadlock                         false
% 54.97/7.52  --bmc1_ucm                              false
% 54.97/7.52  --bmc1_add_unsat_core                   none
% 54.97/7.52  --bmc1_unsat_core_children              false
% 54.97/7.52  --bmc1_unsat_core_extrapolate_axioms    false
% 54.97/7.52  --bmc1_out_stat                         full
% 54.97/7.52  --bmc1_ground_init                      false
% 54.97/7.52  --bmc1_pre_inst_next_state              false
% 54.97/7.52  --bmc1_pre_inst_state                   false
% 54.97/7.52  --bmc1_pre_inst_reach_state             false
% 54.97/7.52  --bmc1_out_unsat_core                   false
% 54.97/7.52  --bmc1_aig_witness_out                  false
% 54.97/7.52  --bmc1_verbose                          false
% 54.97/7.52  --bmc1_dump_clauses_tptp                false
% 54.97/7.52  --bmc1_dump_unsat_core_tptp             false
% 54.97/7.52  --bmc1_dump_file                        -
% 54.97/7.52  --bmc1_ucm_expand_uc_limit              128
% 54.97/7.52  --bmc1_ucm_n_expand_iterations          6
% 54.97/7.52  --bmc1_ucm_extend_mode                  1
% 54.97/7.52  --bmc1_ucm_init_mode                    2
% 54.97/7.52  --bmc1_ucm_cone_mode                    none
% 54.97/7.52  --bmc1_ucm_reduced_relation_type        0
% 54.97/7.52  --bmc1_ucm_relax_model                  4
% 54.97/7.52  --bmc1_ucm_full_tr_after_sat            true
% 54.97/7.52  --bmc1_ucm_expand_neg_assumptions       false
% 54.97/7.52  --bmc1_ucm_layered_model                none
% 54.97/7.52  --bmc1_ucm_max_lemma_size               10
% 54.97/7.52  
% 54.97/7.52  ------ AIG Options
% 54.97/7.52  
% 54.97/7.52  --aig_mode                              false
% 54.97/7.52  
% 54.97/7.52  ------ Instantiation Options
% 54.97/7.52  
% 54.97/7.52  --instantiation_flag                    true
% 54.97/7.52  --inst_sos_flag                         false
% 54.97/7.52  --inst_sos_phase                        true
% 54.97/7.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 54.97/7.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 54.97/7.52  --inst_lit_sel_side                     num_symb
% 54.97/7.52  --inst_solver_per_active                1400
% 54.97/7.52  --inst_solver_calls_frac                1.
% 54.97/7.52  --inst_passive_queue_type               priority_queues
% 54.97/7.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 54.97/7.52  --inst_passive_queues_freq              [25;2]
% 54.97/7.52  --inst_dismatching                      true
% 54.97/7.52  --inst_eager_unprocessed_to_passive     true
% 54.97/7.52  --inst_prop_sim_given                   true
% 54.97/7.52  --inst_prop_sim_new                     false
% 54.97/7.52  --inst_subs_new                         false
% 54.97/7.52  --inst_eq_res_simp                      false
% 54.97/7.52  --inst_subs_given                       false
% 54.97/7.52  --inst_orphan_elimination               true
% 54.97/7.52  --inst_learning_loop_flag               true
% 54.97/7.52  --inst_learning_start                   3000
% 54.97/7.52  --inst_learning_factor                  2
% 54.97/7.52  --inst_start_prop_sim_after_learn       3
% 54.97/7.52  --inst_sel_renew                        solver
% 54.97/7.52  --inst_lit_activity_flag                true
% 54.97/7.52  --inst_restr_to_given                   false
% 54.97/7.52  --inst_activity_threshold               500
% 54.97/7.52  --inst_out_proof                        true
% 54.97/7.52  
% 54.97/7.52  ------ Resolution Options
% 54.97/7.52  
% 54.97/7.52  --resolution_flag                       true
% 54.97/7.52  --res_lit_sel                           adaptive
% 54.97/7.52  --res_lit_sel_side                      none
% 54.97/7.52  --res_ordering                          kbo
% 54.97/7.52  --res_to_prop_solver                    active
% 54.97/7.52  --res_prop_simpl_new                    false
% 54.97/7.52  --res_prop_simpl_given                  true
% 54.97/7.52  --res_passive_queue_type                priority_queues
% 54.97/7.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 54.97/7.52  --res_passive_queues_freq               [15;5]
% 54.97/7.52  --res_forward_subs                      full
% 54.97/7.52  --res_backward_subs                     full
% 54.97/7.52  --res_forward_subs_resolution           true
% 54.97/7.52  --res_backward_subs_resolution          true
% 54.97/7.52  --res_orphan_elimination                true
% 54.97/7.52  --res_time_limit                        2.
% 54.97/7.52  --res_out_proof                         true
% 54.97/7.52  
% 54.97/7.52  ------ Superposition Options
% 54.97/7.52  
% 54.97/7.52  --superposition_flag                    true
% 54.97/7.52  --sup_passive_queue_type                priority_queues
% 54.97/7.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 54.97/7.52  --sup_passive_queues_freq               [8;1;4]
% 54.97/7.52  --demod_completeness_check              fast
% 54.97/7.52  --demod_use_ground                      true
% 54.97/7.52  --sup_to_prop_solver                    passive
% 54.97/7.52  --sup_prop_simpl_new                    true
% 54.97/7.52  --sup_prop_simpl_given                  true
% 54.97/7.52  --sup_fun_splitting                     false
% 54.97/7.52  --sup_smt_interval                      50000
% 54.97/7.52  
% 54.97/7.52  ------ Superposition Simplification Setup
% 54.97/7.52  
% 54.97/7.52  --sup_indices_passive                   []
% 54.97/7.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.97/7.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.97/7.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.97/7.52  --sup_full_triv                         [TrivRules;PropSubs]
% 54.97/7.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.97/7.52  --sup_full_bw                           [BwDemod]
% 54.97/7.52  --sup_immed_triv                        [TrivRules]
% 54.97/7.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 54.97/7.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.97/7.52  --sup_immed_bw_main                     []
% 54.97/7.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 54.97/7.52  --sup_input_triv                        [Unflattening;TrivRules]
% 54.97/7.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.97/7.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 54.97/7.52  
% 54.97/7.52  ------ Combination Options
% 54.97/7.52  
% 54.97/7.52  --comb_res_mult                         3
% 54.97/7.52  --comb_sup_mult                         2
% 54.97/7.52  --comb_inst_mult                        10
% 54.97/7.52  
% 54.97/7.52  ------ Debug Options
% 54.97/7.52  
% 54.97/7.52  --dbg_backtrace                         false
% 54.97/7.52  --dbg_dump_prop_clauses                 false
% 54.97/7.52  --dbg_dump_prop_clauses_file            -
% 54.97/7.52  --dbg_out_stat                          false
% 54.97/7.52  ------ Parsing...
% 54.97/7.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 54.97/7.52  
% 54.97/7.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 54.97/7.52  
% 54.97/7.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 54.97/7.52  
% 54.97/7.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 54.97/7.52  ------ Proving...
% 54.97/7.52  ------ Problem Properties 
% 54.97/7.52  
% 54.97/7.52  
% 54.97/7.52  clauses                                 19
% 54.97/7.52  conjectures                             5
% 54.97/7.52  EPR                                     7
% 54.97/7.52  Horn                                    12
% 54.97/7.52  unary                                   3
% 54.97/7.52  binary                                  6
% 54.97/7.52  lits                                    46
% 54.97/7.52  lits eq                                 5
% 54.97/7.52  fd_pure                                 0
% 54.97/7.52  fd_pseudo                               0
% 54.97/7.52  fd_cond                                 0
% 54.97/7.52  fd_pseudo_cond                          3
% 54.97/7.52  AC symbols                              0
% 54.97/7.52  
% 54.97/7.52  ------ Schedule dynamic 5 is on 
% 54.97/7.52  
% 54.97/7.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 54.97/7.52  
% 54.97/7.52  
% 54.97/7.52  ------ 
% 54.97/7.52  Current options:
% 54.97/7.52  ------ 
% 54.97/7.52  
% 54.97/7.52  ------ Input Options
% 54.97/7.52  
% 54.97/7.52  --out_options                           all
% 54.97/7.52  --tptp_safe_out                         true
% 54.97/7.52  --problem_path                          ""
% 54.97/7.52  --include_path                          ""
% 54.97/7.52  --clausifier                            res/vclausify_rel
% 54.97/7.52  --clausifier_options                    --mode clausify
% 54.97/7.52  --stdin                                 false
% 54.97/7.52  --stats_out                             all
% 54.97/7.52  
% 54.97/7.52  ------ General Options
% 54.97/7.52  
% 54.97/7.52  --fof                                   false
% 54.97/7.52  --time_out_real                         305.
% 54.97/7.52  --time_out_virtual                      -1.
% 54.97/7.52  --symbol_type_check                     false
% 54.97/7.52  --clausify_out                          false
% 54.97/7.52  --sig_cnt_out                           false
% 54.97/7.52  --trig_cnt_out                          false
% 54.97/7.52  --trig_cnt_out_tolerance                1.
% 54.97/7.52  --trig_cnt_out_sk_spl                   false
% 54.97/7.52  --abstr_cl_out                          false
% 54.97/7.52  
% 54.97/7.52  ------ Global Options
% 54.97/7.52  
% 54.97/7.52  --schedule                              default
% 54.97/7.52  --add_important_lit                     false
% 54.97/7.52  --prop_solver_per_cl                    1000
% 54.97/7.52  --min_unsat_core                        false
% 54.97/7.52  --soft_assumptions                      false
% 54.97/7.52  --soft_lemma_size                       3
% 54.97/7.52  --prop_impl_unit_size                   0
% 54.97/7.52  --prop_impl_unit                        []
% 54.97/7.52  --share_sel_clauses                     true
% 54.97/7.52  --reset_solvers                         false
% 54.97/7.52  --bc_imp_inh                            [conj_cone]
% 54.97/7.52  --conj_cone_tolerance                   3.
% 54.97/7.52  --extra_neg_conj                        none
% 54.97/7.52  --large_theory_mode                     true
% 54.97/7.52  --prolific_symb_bound                   200
% 54.97/7.52  --lt_threshold                          2000
% 54.97/7.52  --clause_weak_htbl                      true
% 54.97/7.52  --gc_record_bc_elim                     false
% 54.97/7.52  
% 54.97/7.52  ------ Preprocessing Options
% 54.97/7.52  
% 54.97/7.52  --preprocessing_flag                    true
% 54.97/7.52  --time_out_prep_mult                    0.1
% 54.97/7.52  --splitting_mode                        input
% 54.97/7.52  --splitting_grd                         true
% 54.97/7.52  --splitting_cvd                         false
% 54.97/7.52  --splitting_cvd_svl                     false
% 54.97/7.52  --splitting_nvd                         32
% 54.97/7.52  --sub_typing                            true
% 54.97/7.52  --prep_gs_sim                           true
% 54.97/7.52  --prep_unflatten                        true
% 54.97/7.52  --prep_res_sim                          true
% 54.97/7.52  --prep_upred                            true
% 54.97/7.52  --prep_sem_filter                       exhaustive
% 54.97/7.52  --prep_sem_filter_out                   false
% 54.97/7.52  --pred_elim                             true
% 54.97/7.52  --res_sim_input                         true
% 54.97/7.52  --eq_ax_congr_red                       true
% 54.97/7.52  --pure_diseq_elim                       true
% 54.97/7.52  --brand_transform                       false
% 54.97/7.52  --non_eq_to_eq                          false
% 54.97/7.52  --prep_def_merge                        true
% 54.97/7.52  --prep_def_merge_prop_impl              false
% 54.97/7.52  --prep_def_merge_mbd                    true
% 54.97/7.52  --prep_def_merge_tr_red                 false
% 54.97/7.52  --prep_def_merge_tr_cl                  false
% 54.97/7.52  --smt_preprocessing                     true
% 54.97/7.52  --smt_ac_axioms                         fast
% 54.97/7.52  --preprocessed_out                      false
% 54.97/7.52  --preprocessed_stats                    false
% 54.97/7.52  
% 54.97/7.52  ------ Abstraction refinement Options
% 54.97/7.52  
% 54.97/7.52  --abstr_ref                             []
% 54.97/7.52  --abstr_ref_prep                        false
% 54.97/7.52  --abstr_ref_until_sat                   false
% 54.97/7.52  --abstr_ref_sig_restrict                funpre
% 54.97/7.52  --abstr_ref_af_restrict_to_split_sk     false
% 54.97/7.52  --abstr_ref_under                       []
% 54.97/7.52  
% 54.97/7.52  ------ SAT Options
% 54.97/7.52  
% 54.97/7.52  --sat_mode                              false
% 54.97/7.52  --sat_fm_restart_options                ""
% 54.97/7.52  --sat_gr_def                            false
% 54.97/7.52  --sat_epr_types                         true
% 54.97/7.52  --sat_non_cyclic_types                  false
% 54.97/7.52  --sat_finite_models                     false
% 54.97/7.52  --sat_fm_lemmas                         false
% 54.97/7.52  --sat_fm_prep                           false
% 54.97/7.52  --sat_fm_uc_incr                        true
% 54.97/7.52  --sat_out_model                         small
% 54.97/7.52  --sat_out_clauses                       false
% 54.97/7.52  
% 54.97/7.52  ------ QBF Options
% 54.97/7.52  
% 54.97/7.52  --qbf_mode                              false
% 54.97/7.52  --qbf_elim_univ                         false
% 54.97/7.52  --qbf_dom_inst                          none
% 54.97/7.52  --qbf_dom_pre_inst                      false
% 54.97/7.52  --qbf_sk_in                             false
% 54.97/7.52  --qbf_pred_elim                         true
% 54.97/7.52  --qbf_split                             512
% 54.97/7.52  
% 54.97/7.52  ------ BMC1 Options
% 54.97/7.52  
% 54.97/7.52  --bmc1_incremental                      false
% 54.97/7.52  --bmc1_axioms                           reachable_all
% 54.97/7.52  --bmc1_min_bound                        0
% 54.97/7.52  --bmc1_max_bound                        -1
% 54.97/7.52  --bmc1_max_bound_default                -1
% 54.97/7.52  --bmc1_symbol_reachability              true
% 54.97/7.52  --bmc1_property_lemmas                  false
% 54.97/7.52  --bmc1_k_induction                      false
% 54.97/7.52  --bmc1_non_equiv_states                 false
% 54.97/7.52  --bmc1_deadlock                         false
% 54.97/7.52  --bmc1_ucm                              false
% 54.97/7.52  --bmc1_add_unsat_core                   none
% 54.97/7.52  --bmc1_unsat_core_children              false
% 54.97/7.52  --bmc1_unsat_core_extrapolate_axioms    false
% 54.97/7.52  --bmc1_out_stat                         full
% 54.97/7.52  --bmc1_ground_init                      false
% 54.97/7.52  --bmc1_pre_inst_next_state              false
% 54.97/7.52  --bmc1_pre_inst_state                   false
% 54.97/7.52  --bmc1_pre_inst_reach_state             false
% 54.97/7.52  --bmc1_out_unsat_core                   false
% 54.97/7.52  --bmc1_aig_witness_out                  false
% 54.97/7.52  --bmc1_verbose                          false
% 54.97/7.52  --bmc1_dump_clauses_tptp                false
% 54.97/7.52  --bmc1_dump_unsat_core_tptp             false
% 54.97/7.52  --bmc1_dump_file                        -
% 54.97/7.52  --bmc1_ucm_expand_uc_limit              128
% 54.97/7.52  --bmc1_ucm_n_expand_iterations          6
% 54.97/7.52  --bmc1_ucm_extend_mode                  1
% 54.97/7.52  --bmc1_ucm_init_mode                    2
% 54.97/7.52  --bmc1_ucm_cone_mode                    none
% 54.97/7.52  --bmc1_ucm_reduced_relation_type        0
% 54.97/7.52  --bmc1_ucm_relax_model                  4
% 54.97/7.52  --bmc1_ucm_full_tr_after_sat            true
% 54.97/7.52  --bmc1_ucm_expand_neg_assumptions       false
% 54.97/7.52  --bmc1_ucm_layered_model                none
% 54.97/7.52  --bmc1_ucm_max_lemma_size               10
% 54.97/7.52  
% 54.97/7.52  ------ AIG Options
% 54.97/7.52  
% 54.97/7.52  --aig_mode                              false
% 54.97/7.52  
% 54.97/7.52  ------ Instantiation Options
% 54.97/7.52  
% 54.97/7.52  --instantiation_flag                    true
% 54.97/7.52  --inst_sos_flag                         false
% 54.97/7.52  --inst_sos_phase                        true
% 54.97/7.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 54.97/7.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 54.97/7.52  --inst_lit_sel_side                     none
% 54.97/7.52  --inst_solver_per_active                1400
% 54.97/7.52  --inst_solver_calls_frac                1.
% 54.97/7.52  --inst_passive_queue_type               priority_queues
% 54.97/7.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 54.97/7.52  --inst_passive_queues_freq              [25;2]
% 54.97/7.52  --inst_dismatching                      true
% 54.97/7.52  --inst_eager_unprocessed_to_passive     true
% 54.97/7.52  --inst_prop_sim_given                   true
% 54.97/7.52  --inst_prop_sim_new                     false
% 54.97/7.52  --inst_subs_new                         false
% 54.97/7.52  --inst_eq_res_simp                      false
% 54.97/7.52  --inst_subs_given                       false
% 54.97/7.52  --inst_orphan_elimination               true
% 54.97/7.52  --inst_learning_loop_flag               true
% 54.97/7.52  --inst_learning_start                   3000
% 54.97/7.52  --inst_learning_factor                  2
% 54.97/7.52  --inst_start_prop_sim_after_learn       3
% 54.97/7.52  --inst_sel_renew                        solver
% 54.97/7.52  --inst_lit_activity_flag                true
% 54.97/7.52  --inst_restr_to_given                   false
% 54.97/7.52  --inst_activity_threshold               500
% 54.97/7.52  --inst_out_proof                        true
% 54.97/7.52  
% 54.97/7.52  ------ Resolution Options
% 54.97/7.52  
% 54.97/7.52  --resolution_flag                       false
% 54.97/7.52  --res_lit_sel                           adaptive
% 54.97/7.52  --res_lit_sel_side                      none
% 54.97/7.52  --res_ordering                          kbo
% 54.97/7.52  --res_to_prop_solver                    active
% 54.97/7.52  --res_prop_simpl_new                    false
% 54.97/7.52  --res_prop_simpl_given                  true
% 54.97/7.52  --res_passive_queue_type                priority_queues
% 54.97/7.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 54.97/7.52  --res_passive_queues_freq               [15;5]
% 54.97/7.52  --res_forward_subs                      full
% 54.97/7.52  --res_backward_subs                     full
% 54.97/7.52  --res_forward_subs_resolution           true
% 54.97/7.52  --res_backward_subs_resolution          true
% 54.97/7.52  --res_orphan_elimination                true
% 54.97/7.52  --res_time_limit                        2.
% 54.97/7.52  --res_out_proof                         true
% 54.97/7.52  
% 54.97/7.52  ------ Superposition Options
% 54.97/7.52  
% 54.97/7.52  --superposition_flag                    true
% 54.97/7.52  --sup_passive_queue_type                priority_queues
% 54.97/7.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 54.97/7.52  --sup_passive_queues_freq               [8;1;4]
% 54.97/7.52  --demod_completeness_check              fast
% 54.97/7.52  --demod_use_ground                      true
% 54.97/7.52  --sup_to_prop_solver                    passive
% 54.97/7.52  --sup_prop_simpl_new                    true
% 54.97/7.52  --sup_prop_simpl_given                  true
% 54.97/7.52  --sup_fun_splitting                     false
% 54.97/7.52  --sup_smt_interval                      50000
% 54.97/7.52  
% 54.97/7.52  ------ Superposition Simplification Setup
% 54.97/7.52  
% 54.97/7.52  --sup_indices_passive                   []
% 54.97/7.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.97/7.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.97/7.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.97/7.52  --sup_full_triv                         [TrivRules;PropSubs]
% 54.97/7.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.97/7.52  --sup_full_bw                           [BwDemod]
% 54.97/7.52  --sup_immed_triv                        [TrivRules]
% 54.97/7.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 54.97/7.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.97/7.52  --sup_immed_bw_main                     []
% 54.97/7.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 54.97/7.52  --sup_input_triv                        [Unflattening;TrivRules]
% 54.97/7.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.97/7.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 54.97/7.52  
% 54.97/7.52  ------ Combination Options
% 54.97/7.52  
% 54.97/7.52  --comb_res_mult                         3
% 54.97/7.52  --comb_sup_mult                         2
% 54.97/7.52  --comb_inst_mult                        10
% 54.97/7.52  
% 54.97/7.52  ------ Debug Options
% 54.97/7.52  
% 54.97/7.52  --dbg_backtrace                         false
% 54.97/7.52  --dbg_dump_prop_clauses                 false
% 54.97/7.52  --dbg_dump_prop_clauses_file            -
% 54.97/7.52  --dbg_out_stat                          false
% 54.97/7.52  
% 54.97/7.52  
% 54.97/7.52  
% 54.97/7.52  
% 54.97/7.52  ------ Proving...
% 54.97/7.52  
% 54.97/7.52  
% 54.97/7.52  % SZS status Theorem for theBenchmark.p
% 54.97/7.52  
% 54.97/7.52  % SZS output start CNFRefutation for theBenchmark.p
% 54.97/7.52  
% 54.97/7.52  fof(f2,axiom,(
% 54.97/7.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 54.97/7.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.97/7.52  
% 54.97/7.52  fof(f18,plain,(
% 54.97/7.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 54.97/7.52    inference(nnf_transformation,[],[f2])).
% 54.97/7.52  
% 54.97/7.52  fof(f19,plain,(
% 54.97/7.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 54.97/7.52    inference(flattening,[],[f18])).
% 54.97/7.52  
% 54.97/7.52  fof(f20,plain,(
% 54.97/7.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 54.97/7.52    inference(rectify,[],[f19])).
% 54.97/7.52  
% 54.97/7.52  fof(f21,plain,(
% 54.97/7.52    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 54.97/7.52    introduced(choice_axiom,[])).
% 54.97/7.52  
% 54.97/7.52  fof(f22,plain,(
% 54.97/7.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 54.97/7.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).
% 54.97/7.52  
% 54.97/7.52  fof(f33,plain,(
% 54.97/7.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 54.97/7.52    inference(cnf_transformation,[],[f22])).
% 54.97/7.52  
% 54.97/7.52  fof(f3,axiom,(
% 54.97/7.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 54.97/7.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.97/7.52  
% 54.97/7.52  fof(f36,plain,(
% 54.97/7.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 54.97/7.52    inference(cnf_transformation,[],[f3])).
% 54.97/7.52  
% 54.97/7.52  fof(f50,plain,(
% 54.97/7.52    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 54.97/7.52    inference(definition_unfolding,[],[f33,f36])).
% 54.97/7.52  
% 54.97/7.52  fof(f4,axiom,(
% 54.97/7.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 54.97/7.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.97/7.52  
% 54.97/7.52  fof(f9,plain,(
% 54.97/7.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 54.97/7.52    inference(ennf_transformation,[],[f4])).
% 54.97/7.52  
% 54.97/7.52  fof(f23,plain,(
% 54.97/7.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 54.97/7.52    inference(nnf_transformation,[],[f9])).
% 54.97/7.52  
% 54.97/7.52  fof(f38,plain,(
% 54.97/7.52    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 54.97/7.52    inference(cnf_transformation,[],[f23])).
% 54.97/7.52  
% 54.97/7.52  fof(f1,axiom,(
% 54.97/7.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 54.97/7.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.97/7.52  
% 54.97/7.52  fof(f14,plain,(
% 54.97/7.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 54.97/7.52    inference(nnf_transformation,[],[f1])).
% 54.97/7.52  
% 54.97/7.52  fof(f15,plain,(
% 54.97/7.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 54.97/7.52    inference(rectify,[],[f14])).
% 54.97/7.52  
% 54.97/7.52  fof(f16,plain,(
% 54.97/7.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 54.97/7.52    introduced(choice_axiom,[])).
% 54.97/7.52  
% 54.97/7.52  fof(f17,plain,(
% 54.97/7.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 54.97/7.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 54.97/7.52  
% 54.97/7.52  fof(f28,plain,(
% 54.97/7.52    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 54.97/7.52    inference(cnf_transformation,[],[f17])).
% 54.97/7.52  
% 54.97/7.52  fof(f7,conjecture,(
% 54.97/7.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (~r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 54.97/7.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.97/7.52  
% 54.97/7.52  fof(f8,negated_conjecture,(
% 54.97/7.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (~r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 54.97/7.52    inference(negated_conjecture,[],[f7])).
% 54.97/7.52  
% 54.97/7.52  fof(f12,plain,(
% 54.97/7.52    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & ! [X3] : ((~r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 54.97/7.52    inference(ennf_transformation,[],[f8])).
% 54.97/7.52  
% 54.97/7.52  fof(f13,plain,(
% 54.97/7.52    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : ((~r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 54.97/7.52    inference(flattening,[],[f12])).
% 54.97/7.52  
% 54.97/7.52  fof(f24,plain,(
% 54.97/7.52    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 54.97/7.52    inference(nnf_transformation,[],[f13])).
% 54.97/7.52  
% 54.97/7.52  fof(f26,plain,(
% 54.97/7.52    ( ! [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k3_subset_1(X0,sK4) != X1 & ! [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,sK4)) & (r2_hidden(X3,sK4) | r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(sK4,k1_zfmisc_1(X0)))) )),
% 54.97/7.52    introduced(choice_axiom,[])).
% 54.97/7.52  
% 54.97/7.52  fof(f25,plain,(
% 54.97/7.52    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k3_subset_1(sK2,X2) != sK3 & ! [X3] : (((~r2_hidden(X3,sK3) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | r2_hidden(X3,sK3))) | ~m1_subset_1(X3,sK2)) & m1_subset_1(X2,k1_zfmisc_1(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(sK2)))),
% 54.97/7.52    introduced(choice_axiom,[])).
% 54.97/7.52  
% 54.97/7.52  fof(f27,plain,(
% 54.97/7.52    (k3_subset_1(sK2,sK4) != sK3 & ! [X3] : (((~r2_hidden(X3,sK3) | ~r2_hidden(X3,sK4)) & (r2_hidden(X3,sK4) | r2_hidden(X3,sK3))) | ~m1_subset_1(X3,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 54.97/7.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f26,f25])).
% 54.97/7.52  
% 54.97/7.52  fof(f45,plain,(
% 54.97/7.52    ( ! [X3] : (r2_hidden(X3,sK4) | r2_hidden(X3,sK3) | ~m1_subset_1(X3,sK2)) )),
% 54.97/7.52    inference(cnf_transformation,[],[f27])).
% 54.97/7.52  
% 54.97/7.52  fof(f34,plain,(
% 54.97/7.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 54.97/7.52    inference(cnf_transformation,[],[f22])).
% 54.97/7.52  
% 54.97/7.52  fof(f49,plain,(
% 54.97/7.52    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 54.97/7.52    inference(definition_unfolding,[],[f34,f36])).
% 54.97/7.52  
% 54.97/7.52  fof(f43,plain,(
% 54.97/7.52    m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 54.97/7.52    inference(cnf_transformation,[],[f27])).
% 54.97/7.52  
% 54.97/7.52  fof(f5,axiom,(
% 54.97/7.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 54.97/7.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.97/7.52  
% 54.97/7.52  fof(f10,plain,(
% 54.97/7.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 54.97/7.52    inference(ennf_transformation,[],[f5])).
% 54.97/7.52  
% 54.97/7.52  fof(f41,plain,(
% 54.97/7.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 54.97/7.52    inference(cnf_transformation,[],[f10])).
% 54.97/7.52  
% 54.97/7.52  fof(f54,plain,(
% 54.97/7.52    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 54.97/7.52    inference(definition_unfolding,[],[f41,f36])).
% 54.97/7.52  
% 54.97/7.52  fof(f44,plain,(
% 54.97/7.52    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 54.97/7.52    inference(cnf_transformation,[],[f27])).
% 54.97/7.52  
% 54.97/7.52  fof(f6,axiom,(
% 54.97/7.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 54.97/7.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.97/7.52  
% 54.97/7.52  fof(f11,plain,(
% 54.97/7.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 54.97/7.52    inference(ennf_transformation,[],[f6])).
% 54.97/7.52  
% 54.97/7.52  fof(f42,plain,(
% 54.97/7.52    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 54.97/7.52    inference(cnf_transformation,[],[f11])).
% 54.97/7.52  
% 54.97/7.52  fof(f35,plain,(
% 54.97/7.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 54.97/7.52    inference(cnf_transformation,[],[f22])).
% 54.97/7.52  
% 54.97/7.52  fof(f48,plain,(
% 54.97/7.52    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 54.97/7.52    inference(definition_unfolding,[],[f35,f36])).
% 54.97/7.52  
% 54.97/7.52  fof(f46,plain,(
% 54.97/7.52    ( ! [X3] : (~r2_hidden(X3,sK3) | ~r2_hidden(X3,sK4) | ~m1_subset_1(X3,sK2)) )),
% 54.97/7.52    inference(cnf_transformation,[],[f27])).
% 54.97/7.52  
% 54.97/7.52  fof(f31,plain,(
% 54.97/7.52    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 54.97/7.52    inference(cnf_transformation,[],[f22])).
% 54.97/7.52  
% 54.97/7.52  fof(f52,plain,(
% 54.97/7.52    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 54.97/7.52    inference(definition_unfolding,[],[f31,f36])).
% 54.97/7.52  
% 54.97/7.52  fof(f56,plain,(
% 54.97/7.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 54.97/7.52    inference(equality_resolution,[],[f52])).
% 54.97/7.52  
% 54.97/7.52  fof(f32,plain,(
% 54.97/7.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 54.97/7.52    inference(cnf_transformation,[],[f22])).
% 54.97/7.52  
% 54.97/7.52  fof(f51,plain,(
% 54.97/7.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 54.97/7.52    inference(definition_unfolding,[],[f32,f36])).
% 54.97/7.52  
% 54.97/7.52  fof(f55,plain,(
% 54.97/7.52    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 54.97/7.52    inference(equality_resolution,[],[f51])).
% 54.97/7.52  
% 54.97/7.52  fof(f47,plain,(
% 54.97/7.52    k3_subset_1(sK2,sK4) != sK3),
% 54.97/7.52    inference(cnf_transformation,[],[f27])).
% 54.97/7.52  
% 54.97/7.52  cnf(c_4,plain,
% 54.97/7.52      ( r2_hidden(sK1(X0,X1,X2),X0)
% 54.97/7.52      | r2_hidden(sK1(X0,X1,X2),X2)
% 54.97/7.52      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 54.97/7.52      inference(cnf_transformation,[],[f50]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_832,plain,
% 54.97/7.52      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 54.97/7.52      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_10,plain,
% 54.97/7.52      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 54.97/7.52      inference(cnf_transformation,[],[f38]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_1,plain,
% 54.97/7.52      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 54.97/7.52      inference(cnf_transformation,[],[f28]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_103,plain,
% 54.97/7.52      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 54.97/7.52      inference(global_propositional_subsumption,
% 54.97/7.52                [status(thm)],
% 54.97/7.52                [c_10,c_1]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_104,plain,
% 54.97/7.52      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 54.97/7.52      inference(renaming,[status(thm)],[c_103]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_819,plain,
% 54.97/7.52      ( m1_subset_1(X0,X1) = iProver_top
% 54.97/7.52      | r2_hidden(X0,X1) != iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_104]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_2977,plain,
% 54.97/7.52      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 54.97/7.52      | m1_subset_1(sK1(X0,X1,X2),X0) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_832,c_819]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_16,negated_conjecture,
% 54.97/7.52      ( ~ m1_subset_1(X0,sK2) | r2_hidden(X0,sK3) | r2_hidden(X0,sK4) ),
% 54.97/7.52      inference(cnf_transformation,[],[f45]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_822,plain,
% 54.97/7.52      ( m1_subset_1(X0,sK2) != iProver_top
% 54.97/7.52      | r2_hidden(X0,sK3) = iProver_top
% 54.97/7.52      | r2_hidden(X0,sK4) = iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_24170,plain,
% 54.97/7.52      ( k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) = X1
% 54.97/7.52      | r2_hidden(sK1(sK2,X0,X1),X1) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK2,X0,X1),sK3) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK2,X0,X1),sK4) = iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_2977,c_822]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_3,plain,
% 54.97/7.52      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 54.97/7.52      | r2_hidden(sK1(X0,X1,X2),X2)
% 54.97/7.52      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 54.97/7.52      inference(cnf_transformation,[],[f49]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_833,plain,
% 54.97/7.52      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 54.97/7.52      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_24847,plain,
% 54.97/7.52      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = X0
% 54.97/7.52      | r2_hidden(sK1(sK2,sK3,X0),X0) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK2,sK3,X0),sK4) = iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_24170,c_833]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_18,negated_conjecture,
% 54.97/7.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
% 54.97/7.52      inference(cnf_transformation,[],[f43]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_820,plain,
% 54.97/7.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_12,plain,
% 54.97/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 54.97/7.52      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 54.97/7.52      inference(cnf_transformation,[],[f54]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_825,plain,
% 54.97/7.52      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 54.97/7.52      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_1566,plain,
% 54.97/7.52      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = k3_subset_1(sK2,sK3) ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_820,c_825]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_24991,plain,
% 54.97/7.52      ( k3_subset_1(sK2,sK3) = X0
% 54.97/7.52      | r2_hidden(sK1(sK2,sK3,X0),X0) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK2,sK3,X0),sK4) = iProver_top ),
% 54.97/7.52      inference(demodulation,[status(thm)],[c_24847,c_1566]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_17,negated_conjecture,
% 54.97/7.52      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 54.97/7.52      inference(cnf_transformation,[],[f44]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_821,plain,
% 54.97/7.52      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_13,plain,
% 54.97/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 54.97/7.52      | ~ r2_hidden(X2,X0)
% 54.97/7.52      | r2_hidden(X2,X1) ),
% 54.97/7.52      inference(cnf_transformation,[],[f42]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_824,plain,
% 54.97/7.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 54.97/7.52      | r2_hidden(X2,X0) != iProver_top
% 54.97/7.52      | r2_hidden(X2,X1) = iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_1250,plain,
% 54.97/7.52      ( r2_hidden(X0,sK4) != iProver_top
% 54.97/7.52      | r2_hidden(X0,sK2) = iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_821,c_824]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_25226,plain,
% 54.97/7.52      ( k3_subset_1(sK2,sK3) = X0
% 54.97/7.52      | r2_hidden(sK1(sK2,sK3,X0),X0) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK2,sK3,X0),sK2) = iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_24991,c_1250]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_25390,plain,
% 54.97/7.52      ( k3_subset_1(sK2,sK3) = sK4
% 54.97/7.52      | r2_hidden(sK1(sK2,sK3,sK4),sK2) = iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_25226,c_1250]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_2,plain,
% 54.97/7.52      ( ~ r2_hidden(sK1(X0,X1,X2),X0)
% 54.97/7.52      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 54.97/7.52      | r2_hidden(sK1(X0,X1,X2),X1)
% 54.97/7.52      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 54.97/7.52      inference(cnf_transformation,[],[f48]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_834,plain,
% 54.97/7.52      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 54.97/7.52      | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_26000,plain,
% 54.97/7.52      ( k3_subset_1(sK2,sK3) = sK4
% 54.97/7.52      | k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = sK4
% 54.97/7.52      | r2_hidden(sK1(sK2,sK3,sK4),sK3) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK2,sK3,sK4),sK4) != iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_25390,c_834]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_26005,plain,
% 54.97/7.52      ( k3_subset_1(sK2,sK3) = sK4
% 54.97/7.52      | r2_hidden(sK1(sK2,sK3,sK4),sK3) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK2,sK3,sK4),sK4) != iProver_top ),
% 54.97/7.52      inference(demodulation,[status(thm)],[c_26000,c_1566]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_25245,plain,
% 54.97/7.52      ( k3_subset_1(sK2,sK3) = sK4
% 54.97/7.52      | r2_hidden(sK1(sK2,sK3,sK4),sK4) = iProver_top
% 54.97/7.52      | iProver_top != iProver_top ),
% 54.97/7.52      inference(equality_factoring,[status(thm)],[c_24991]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_25247,plain,
% 54.97/7.52      ( k3_subset_1(sK2,sK3) = sK4
% 54.97/7.52      | r2_hidden(sK1(sK2,sK3,sK4),sK4) = iProver_top ),
% 54.97/7.52      inference(equality_resolution_simp,[status(thm)],[c_25245]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_27300,plain,
% 54.97/7.52      ( r2_hidden(sK1(sK2,sK3,sK4),sK3) = iProver_top
% 54.97/7.52      | k3_subset_1(sK2,sK3) = sK4 ),
% 54.97/7.52      inference(global_propositional_subsumption,
% 54.97/7.52                [status(thm)],
% 54.97/7.52                [c_26005,c_25247]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_27301,plain,
% 54.97/7.52      ( k3_subset_1(sK2,sK3) = sK4
% 54.97/7.52      | r2_hidden(sK1(sK2,sK3,sK4),sK3) = iProver_top ),
% 54.97/7.52      inference(renaming,[status(thm)],[c_27300]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_1251,plain,
% 54.97/7.52      ( r2_hidden(X0,sK3) != iProver_top
% 54.97/7.52      | r2_hidden(X0,sK2) = iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_820,c_824]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_2974,plain,
% 54.97/7.52      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = sK3
% 54.97/7.52      | r2_hidden(sK1(X0,X1,sK3),X0) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(X0,X1,sK3),sK2) = iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_832,c_1251]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_6993,plain,
% 54.97/7.52      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),sK2) = iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_2974,c_1251]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_7086,plain,
% 54.97/7.52      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 54.97/7.52      | m1_subset_1(sK1(sK3,X0,sK3),sK2) = iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_6993,c_819]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_17292,plain,
% 54.97/7.52      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),sK3) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),sK4) = iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_7086,c_822]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_1987,plain,
% 54.97/7.52      ( r2_hidden(sK1(sK3,X0,X1),X1)
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,X1),sK3)
% 54.97/7.52      | k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = X1 ),
% 54.97/7.52      inference(instantiation,[status(thm)],[c_4]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_2713,plain,
% 54.97/7.52      ( r2_hidden(sK1(sK3,X0,sK3),sK3)
% 54.97/7.52      | k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3 ),
% 54.97/7.52      inference(instantiation,[status(thm)],[c_1987]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_2715,plain,
% 54.97/7.52      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),sK3) = iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_2713]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_19331,plain,
% 54.97/7.52      ( r2_hidden(sK1(sK3,X0,sK3),sK3) = iProver_top
% 54.97/7.52      | k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3 ),
% 54.97/7.52      inference(global_propositional_subsumption,
% 54.97/7.52                [status(thm)],
% 54.97/7.52                [c_17292,c_2715]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_19332,plain,
% 54.97/7.52      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),sK3) = iProver_top ),
% 54.97/7.52      inference(renaming,[status(thm)],[c_19331]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_19339,plain,
% 54.97/7.52      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),X0) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),sK3) != iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_19332,c_834]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_19346,plain,
% 54.97/7.52      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),X0) = iProver_top ),
% 54.97/7.52      inference(forward_subsumption_resolution,
% 54.97/7.52                [status(thm)],
% 54.97/7.52                [c_19339,c_19332]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_15,negated_conjecture,
% 54.97/7.52      ( ~ m1_subset_1(X0,sK2)
% 54.97/7.52      | ~ r2_hidden(X0,sK3)
% 54.97/7.52      | ~ r2_hidden(X0,sK4) ),
% 54.97/7.52      inference(cnf_transformation,[],[f46]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_823,plain,
% 54.97/7.52      ( m1_subset_1(X0,sK2) != iProver_top
% 54.97/7.52      | r2_hidden(X0,sK3) != iProver_top
% 54.97/7.52      | r2_hidden(X0,sK4) != iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_17293,plain,
% 54.97/7.52      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),sK3) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),sK4) != iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_7086,c_823]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_19,plain,
% 54.97/7.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_1451,plain,
% 54.97/7.52      ( ~ m1_subset_1(sK1(X0,X1,sK3),sK2)
% 54.97/7.52      | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
% 54.97/7.52      | ~ r2_hidden(sK1(X0,X1,sK3),sK4) ),
% 54.97/7.52      inference(instantiation,[status(thm)],[c_15]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_5323,plain,
% 54.97/7.52      ( ~ m1_subset_1(sK1(sK3,X0,sK3),sK2)
% 54.97/7.52      | ~ r2_hidden(sK1(sK3,X0,sK3),sK3)
% 54.97/7.52      | ~ r2_hidden(sK1(sK3,X0,sK3),sK4) ),
% 54.97/7.52      inference(instantiation,[status(thm)],[c_1451]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_5326,plain,
% 54.97/7.52      ( m1_subset_1(sK1(sK3,X0,sK3),sK2) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),sK3) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),sK4) != iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_5323]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_2683,plain,
% 54.97/7.52      ( m1_subset_1(sK1(sK3,X0,X1),sK2)
% 54.97/7.52      | ~ r2_hidden(sK1(sK3,X0,X1),sK2) ),
% 54.97/7.52      inference(instantiation,[status(thm)],[c_104]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_7859,plain,
% 54.97/7.52      ( m1_subset_1(sK1(sK3,X0,sK3),sK2)
% 54.97/7.52      | ~ r2_hidden(sK1(sK3,X0,sK3),sK2) ),
% 54.97/7.52      inference(instantiation,[status(thm)],[c_2683]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_7863,plain,
% 54.97/7.52      ( m1_subset_1(sK1(sK3,X0,sK3),sK2) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),sK2) != iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_7859]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_3125,plain,
% 54.97/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
% 54.97/7.52      | ~ r2_hidden(sK1(X1,X2,sK3),X0)
% 54.97/7.52      | r2_hidden(sK1(X1,X2,sK3),sK2) ),
% 54.97/7.52      inference(instantiation,[status(thm)],[c_13]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_8974,plain,
% 54.97/7.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
% 54.97/7.52      | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
% 54.97/7.52      | r2_hidden(sK1(X0,X1,sK3),sK2) ),
% 54.97/7.52      inference(instantiation,[status(thm)],[c_3125]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_15967,plain,
% 54.97/7.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
% 54.97/7.52      | ~ r2_hidden(sK1(sK3,X0,sK3),sK3)
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),sK2) ),
% 54.97/7.52      inference(instantiation,[status(thm)],[c_8974]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_15971,plain,
% 54.97/7.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),sK3) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),sK2) = iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_15967]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_17311,plain,
% 54.97/7.52      ( r2_hidden(sK1(sK3,X0,sK3),sK3) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),sK4) != iProver_top ),
% 54.97/7.52      inference(global_propositional_subsumption,
% 54.97/7.52                [status(thm)],
% 54.97/7.52                [c_17293,c_19,c_5326,c_7863,c_15971]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_17322,plain,
% 54.97/7.52      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),sK3) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),sK4) != iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_832,c_17311]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_17340,plain,
% 54.97/7.52      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 54.97/7.52      | r2_hidden(sK1(sK3,X0,sK3),sK4) != iProver_top ),
% 54.97/7.52      inference(forward_subsumption_resolution,
% 54.97/7.52                [status(thm)],
% 54.97/7.52                [c_17322,c_17311]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_21971,plain,
% 54.97/7.52      ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) = sK3 ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_19346,c_17340]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_6,plain,
% 54.97/7.52      ( ~ r2_hidden(X0,X1)
% 54.97/7.52      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 54.97/7.52      inference(cnf_transformation,[],[f56]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_830,plain,
% 54.97/7.52      ( r2_hidden(X0,X1) != iProver_top
% 54.97/7.52      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_69764,plain,
% 54.97/7.52      ( r2_hidden(X0,sK3) != iProver_top
% 54.97/7.52      | r2_hidden(X0,sK4) != iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_21971,c_830]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_72696,plain,
% 54.97/7.52      ( k3_subset_1(sK2,sK3) = sK4
% 54.97/7.52      | r2_hidden(sK1(sK2,sK3,sK4),sK4) != iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_27301,c_69764]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_80629,plain,
% 54.97/7.52      ( k3_subset_1(sK2,sK3) = sK4 ),
% 54.97/7.52      inference(global_propositional_subsumption,
% 54.97/7.52                [status(thm)],
% 54.97/7.52                [c_72696,c_25247]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_80692,plain,
% 54.97/7.52      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = sK4 ),
% 54.97/7.52      inference(demodulation,[status(thm)],[c_80629,c_1566]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_5,plain,
% 54.97/7.52      ( ~ r2_hidden(X0,X1)
% 54.97/7.52      | r2_hidden(X0,X2)
% 54.97/7.52      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 54.97/7.52      inference(cnf_transformation,[],[f55]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_831,plain,
% 54.97/7.52      ( r2_hidden(X0,X1) != iProver_top
% 54.97/7.52      | r2_hidden(X0,X2) = iProver_top
% 54.97/7.52      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_3090,plain,
% 54.97/7.52      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X3
% 54.97/7.52      | r2_hidden(sK1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X1) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X3) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X2) = iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_831,c_833]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_32888,plain,
% 54.97/7.52      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X2
% 54.97/7.52      | r2_hidden(sK1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X2) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X1) = iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_832,c_3090]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_231331,plain,
% 54.97/7.52      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)))) = X0
% 54.97/7.52      | r2_hidden(sK1(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)),X0),sK3) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK2,sK4,X0),X0) = iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_80692,c_32888]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_1565,plain,
% 54.97/7.52      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) = k3_subset_1(sK2,sK4) ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_821,c_825]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_232184,plain,
% 54.97/7.52      ( k3_subset_1(sK2,sK4) = X0
% 54.97/7.52      | r2_hidden(sK1(sK2,sK4,X0),X0) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK2,sK4,X0),sK3) = iProver_top ),
% 54.97/7.52      inference(light_normalisation,
% 54.97/7.52                [status(thm)],
% 54.97/7.52                [c_231331,c_1565,c_80692]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_233708,plain,
% 54.97/7.52      ( k3_subset_1(sK2,sK4) = X0
% 54.97/7.52      | r2_hidden(sK1(sK2,sK4,X0),X0) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK2,sK4,X0),sK2) = iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_232184,c_1251]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_234063,plain,
% 54.97/7.52      ( k3_subset_1(sK2,sK4) = sK3
% 54.97/7.52      | r2_hidden(sK1(sK2,sK4,sK3),sK2) = iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_233708,c_1251]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_14,negated_conjecture,
% 54.97/7.52      ( k3_subset_1(sK2,sK4) != sK3 ),
% 54.97/7.52      inference(cnf_transformation,[],[f47]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_156033,plain,
% 54.97/7.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
% 54.97/7.52      | ~ r2_hidden(sK1(X0,sK4,sK3),sK3)
% 54.97/7.52      | r2_hidden(sK1(X0,sK4,sK3),sK2) ),
% 54.97/7.52      inference(instantiation,[status(thm)],[c_8974]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_156034,plain,
% 54.97/7.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(X0,sK4,sK3),sK3) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(X0,sK4,sK3),sK2) = iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_156033]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_156036,plain,
% 54.97/7.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK2,sK4,sK3),sK3) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK2,sK4,sK3),sK2) = iProver_top ),
% 54.97/7.52      inference(instantiation,[status(thm)],[c_156034]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_233754,plain,
% 54.97/7.52      ( k3_subset_1(sK2,sK4) = sK3
% 54.97/7.52      | r2_hidden(sK1(sK2,sK4,sK3),sK3) = iProver_top
% 54.97/7.52      | iProver_top != iProver_top ),
% 54.97/7.52      inference(equality_factoring,[status(thm)],[c_232184]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_233756,plain,
% 54.97/7.52      ( k3_subset_1(sK2,sK4) = sK3
% 54.97/7.52      | r2_hidden(sK1(sK2,sK4,sK3),sK3) = iProver_top ),
% 54.97/7.52      inference(equality_resolution_simp,[status(thm)],[c_233754]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_234518,plain,
% 54.97/7.52      ( r2_hidden(sK1(sK2,sK4,sK3),sK2) = iProver_top ),
% 54.97/7.52      inference(global_propositional_subsumption,
% 54.97/7.52                [status(thm)],
% 54.97/7.52                [c_234063,c_19,c_14,c_156036,c_233756]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_234525,plain,
% 54.97/7.52      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) = sK3
% 54.97/7.52      | r2_hidden(sK1(sK2,sK4,sK3),sK3) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK2,sK4,sK3),sK4) = iProver_top ),
% 54.97/7.52      inference(superposition,[status(thm)],[c_234518,c_834]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_234534,plain,
% 54.97/7.52      ( k3_subset_1(sK2,sK4) = sK3
% 54.97/7.52      | r2_hidden(sK1(sK2,sK4,sK3),sK3) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK2,sK4,sK3),sK4) = iProver_top ),
% 54.97/7.52      inference(demodulation,[status(thm)],[c_234525,c_1565]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_12079,plain,
% 54.97/7.52      ( ~ m1_subset_1(sK1(X0,sK4,sK3),sK2)
% 54.97/7.52      | ~ r2_hidden(sK1(X0,sK4,sK3),sK3)
% 54.97/7.52      | ~ r2_hidden(sK1(X0,sK4,sK3),sK4) ),
% 54.97/7.52      inference(instantiation,[status(thm)],[c_1451]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_12084,plain,
% 54.97/7.52      ( m1_subset_1(sK1(X0,sK4,sK3),sK2) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(X0,sK4,sK3),sK3) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(X0,sK4,sK3),sK4) != iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_12079]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_12086,plain,
% 54.97/7.52      ( m1_subset_1(sK1(sK2,sK4,sK3),sK2) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK2,sK4,sK3),sK3) != iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK2,sK4,sK3),sK4) != iProver_top ),
% 54.97/7.52      inference(instantiation,[status(thm)],[c_12084]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_1587,plain,
% 54.97/7.52      ( m1_subset_1(sK1(X0,X1,sK3),sK2)
% 54.97/7.52      | ~ r2_hidden(sK1(X0,X1,sK3),sK2) ),
% 54.97/7.52      inference(instantiation,[status(thm)],[c_104]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_11595,plain,
% 54.97/7.52      ( m1_subset_1(sK1(X0,sK4,sK3),sK2)
% 54.97/7.52      | ~ r2_hidden(sK1(X0,sK4,sK3),sK2) ),
% 54.97/7.52      inference(instantiation,[status(thm)],[c_1587]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_11596,plain,
% 54.97/7.52      ( m1_subset_1(sK1(X0,sK4,sK3),sK2) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(X0,sK4,sK3),sK2) != iProver_top ),
% 54.97/7.52      inference(predicate_to_equality,[status(thm)],[c_11595]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(c_11598,plain,
% 54.97/7.52      ( m1_subset_1(sK1(sK2,sK4,sK3),sK2) = iProver_top
% 54.97/7.52      | r2_hidden(sK1(sK2,sK4,sK3),sK2) != iProver_top ),
% 54.97/7.52      inference(instantiation,[status(thm)],[c_11596]) ).
% 54.97/7.52  
% 54.97/7.52  cnf(contradiction,plain,
% 54.97/7.52      ( $false ),
% 54.97/7.52      inference(minisat,
% 54.97/7.52                [status(thm)],
% 54.97/7.52                [c_234534,c_233756,c_156036,c_12086,c_11598,c_14,c_19]) ).
% 54.97/7.52  
% 54.97/7.52  
% 54.97/7.52  % SZS output end CNFRefutation for theBenchmark.p
% 54.97/7.52  
% 54.97/7.52  ------                               Statistics
% 54.97/7.52  
% 54.97/7.52  ------ General
% 54.97/7.52  
% 54.97/7.52  abstr_ref_over_cycles:                  0
% 54.97/7.52  abstr_ref_under_cycles:                 0
% 54.97/7.52  gc_basic_clause_elim:                   0
% 54.97/7.52  forced_gc_time:                         0
% 54.97/7.52  parsing_time:                           0.011
% 54.97/7.52  unif_index_cands_time:                  0.
% 54.97/7.52  unif_index_add_time:                    0.
% 54.97/7.52  orderings_time:                         0.
% 54.97/7.52  out_proof_time:                         0.028
% 54.97/7.52  total_time:                             6.934
% 54.97/7.52  num_of_symbols:                         43
% 54.97/7.52  num_of_terms:                           256995
% 54.97/7.52  
% 54.97/7.52  ------ Preprocessing
% 54.97/7.52  
% 54.97/7.52  num_of_splits:                          0
% 54.97/7.52  num_of_split_atoms:                     0
% 54.97/7.52  num_of_reused_defs:                     0
% 54.97/7.52  num_eq_ax_congr_red:                    16
% 54.97/7.52  num_of_sem_filtered_clauses:            1
% 54.97/7.52  num_of_subtypes:                        0
% 54.97/7.52  monotx_restored_types:                  0
% 54.97/7.52  sat_num_of_epr_types:                   0
% 54.97/7.52  sat_num_of_non_cyclic_types:            0
% 54.97/7.52  sat_guarded_non_collapsed_types:        0
% 54.97/7.52  num_pure_diseq_elim:                    0
% 54.97/7.52  simp_replaced_by:                       0
% 54.97/7.52  res_preprocessed:                       72
% 54.97/7.52  prep_upred:                             0
% 54.97/7.52  prep_unflattend:                        32
% 54.97/7.52  smt_new_axioms:                         0
% 54.97/7.52  pred_elim_cands:                        3
% 54.97/7.52  pred_elim:                              0
% 54.97/7.52  pred_elim_cl:                           0
% 54.97/7.52  pred_elim_cycles:                       1
% 54.97/7.52  merged_defs:                            0
% 54.97/7.52  merged_defs_ncl:                        0
% 54.97/7.52  bin_hyper_res:                          0
% 54.97/7.52  prep_cycles:                            3
% 54.97/7.52  pred_elim_time:                         0.004
% 54.97/7.52  splitting_time:                         0.
% 54.97/7.52  sem_filter_time:                        0.
% 54.97/7.52  monotx_time:                            0.001
% 54.97/7.52  subtype_inf_time:                       0.
% 54.97/7.52  
% 54.97/7.52  ------ Problem properties
% 54.97/7.52  
% 54.97/7.52  clauses:                                19
% 54.97/7.52  conjectures:                            5
% 54.97/7.52  epr:                                    7
% 54.97/7.52  horn:                                   12
% 54.97/7.52  ground:                                 3
% 54.97/7.52  unary:                                  3
% 54.97/7.52  binary:                                 6
% 54.97/7.52  lits:                                   46
% 54.97/7.52  lits_eq:                                5
% 54.97/7.52  fd_pure:                                0
% 54.97/7.52  fd_pseudo:                              0
% 54.97/7.52  fd_cond:                                0
% 54.97/7.52  fd_pseudo_cond:                         3
% 54.97/7.52  ac_symbols:                             0
% 54.97/7.52  
% 54.97/7.52  ------ Propositional Solver
% 54.97/7.52  
% 54.97/7.52  prop_solver_calls:                      62
% 54.97/7.52  prop_fast_solver_calls:                 3082
% 54.97/7.52  smt_solver_calls:                       0
% 54.97/7.52  smt_fast_solver_calls:                  0
% 54.97/7.52  prop_num_of_clauses:                    61733
% 54.97/7.52  prop_preprocess_simplified:             103692
% 54.97/7.52  prop_fo_subsumed:                       138
% 54.97/7.52  prop_solver_time:                       0.
% 54.97/7.52  smt_solver_time:                        0.
% 54.97/7.52  smt_fast_solver_time:                   0.
% 54.97/7.52  prop_fast_solver_time:                  0.
% 54.97/7.52  prop_unsat_core_time:                   0.004
% 54.97/7.52  
% 54.97/7.52  ------ QBF
% 54.97/7.52  
% 54.97/7.52  qbf_q_res:                              0
% 54.97/7.52  qbf_num_tautologies:                    0
% 54.97/7.52  qbf_prep_cycles:                        0
% 54.97/7.52  
% 54.97/7.52  ------ BMC1
% 54.97/7.52  
% 54.97/7.52  bmc1_current_bound:                     -1
% 54.97/7.52  bmc1_last_solved_bound:                 -1
% 54.97/7.52  bmc1_unsat_core_size:                   -1
% 54.97/7.52  bmc1_unsat_core_parents_size:           -1
% 54.97/7.52  bmc1_merge_next_fun:                    0
% 54.97/7.52  bmc1_unsat_core_clauses_time:           0.
% 54.97/7.52  
% 54.97/7.52  ------ Instantiation
% 54.97/7.52  
% 54.97/7.52  inst_num_of_clauses:                    1358
% 54.97/7.52  inst_num_in_passive:                    546
% 54.97/7.52  inst_num_in_active:                     2663
% 54.97/7.52  inst_num_in_unprocessed:                380
% 54.97/7.52  inst_num_of_loops:                      3459
% 54.97/7.52  inst_num_of_learning_restarts:          1
% 54.97/7.52  inst_num_moves_active_passive:          795
% 54.97/7.52  inst_lit_activity:                      0
% 54.97/7.52  inst_lit_activity_moves:                0
% 54.97/7.52  inst_num_tautologies:                   0
% 54.97/7.52  inst_num_prop_implied:                  0
% 54.97/7.52  inst_num_existing_simplified:           0
% 54.97/7.52  inst_num_eq_res_simplified:             0
% 54.97/7.52  inst_num_child_elim:                    0
% 54.97/7.52  inst_num_of_dismatching_blockings:      34980
% 54.97/7.52  inst_num_of_non_proper_insts:           15595
% 54.97/7.52  inst_num_of_duplicates:                 0
% 54.97/7.52  inst_inst_num_from_inst_to_res:         0
% 54.97/7.52  inst_dismatching_checking_time:         0.
% 54.97/7.52  
% 54.97/7.52  ------ Resolution
% 54.97/7.52  
% 54.97/7.52  res_num_of_clauses:                     26
% 54.97/7.52  res_num_in_passive:                     26
% 54.97/7.52  res_num_in_active:                      0
% 54.97/7.52  res_num_of_loops:                       75
% 54.97/7.52  res_forward_subset_subsumed:            398
% 54.97/7.52  res_backward_subset_subsumed:           4
% 54.97/7.52  res_forward_subsumed:                   1
% 54.97/7.52  res_backward_subsumed:                  0
% 54.97/7.52  res_forward_subsumption_resolution:     0
% 54.97/7.52  res_backward_subsumption_resolution:    0
% 54.97/7.52  res_clause_to_clause_subsumption:       86560
% 54.97/7.52  res_orphan_elimination:                 0
% 54.97/7.52  res_tautology_del:                      2590
% 54.97/7.52  res_num_eq_res_simplified:              0
% 54.97/7.52  res_num_sel_changes:                    0
% 54.97/7.52  res_moves_from_active_to_pass:          0
% 54.97/7.52  
% 54.97/7.52  ------ Superposition
% 54.97/7.52  
% 54.97/7.52  sup_time_total:                         0.
% 54.97/7.52  sup_time_generating:                    0.
% 54.97/7.52  sup_time_sim_full:                      0.
% 54.97/7.52  sup_time_sim_immed:                     0.
% 54.97/7.52  
% 54.97/7.52  sup_num_of_clauses:                     6718
% 54.97/7.52  sup_num_in_active:                      578
% 54.97/7.52  sup_num_in_passive:                     6140
% 54.97/7.52  sup_num_of_loops:                       690
% 54.97/7.52  sup_fw_superposition:                   4464
% 54.97/7.52  sup_bw_superposition:                   8111
% 54.97/7.52  sup_immediate_simplified:               4585
% 54.97/7.52  sup_given_eliminated:                   17
% 54.97/7.52  comparisons_done:                       0
% 54.97/7.52  comparisons_avoided:                    167
% 54.97/7.52  
% 54.97/7.52  ------ Simplifications
% 54.97/7.52  
% 54.97/7.52  
% 54.97/7.52  sim_fw_subset_subsumed:                 1258
% 54.97/7.52  sim_bw_subset_subsumed:                 75
% 54.97/7.52  sim_fw_subsumed:                        2299
% 54.97/7.52  sim_bw_subsumed:                        159
% 54.97/7.52  sim_fw_subsumption_res:                 165
% 54.97/7.52  sim_bw_subsumption_res:                 13
% 54.97/7.52  sim_tautology_del:                      383
% 54.97/7.52  sim_eq_tautology_del:                   71
% 54.97/7.52  sim_eq_res_simp:                        95
% 54.97/7.52  sim_fw_demodulated:                     340
% 54.97/7.52  sim_bw_demodulated:                     117
% 54.97/7.52  sim_light_normalised:                   1071
% 54.97/7.52  sim_joinable_taut:                      0
% 54.97/7.52  sim_joinable_simp:                      0
% 54.97/7.52  sim_ac_normalised:                      0
% 54.97/7.52  sim_smt_subsumption:                    0
% 54.97/7.52  
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 11:41:03 EST 2020

% Result     : Timeout 59.21s
% Output     : None 
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
               => ( r2_hidden(X3,X1)
                <=> ~ r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> ~ r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> ~ r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> ~ r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | r2_hidden(X3,X2) )
                & ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | r2_hidden(X3,X2) )
                & ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( k3_subset_1(X0,sK4) != X1
        & ! [X3] :
            ( ( ( r2_hidden(X3,X1)
                | r2_hidden(X3,sK4) )
              & ( ~ r2_hidden(X3,sK4)
                | ~ r2_hidden(X3,X1) ) )
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | r2_hidden(X3,X2) )
                  & ( ~ r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k3_subset_1(sK2,X2) != sK3
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK3)
                  | r2_hidden(X3,X2) )
                & ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK3) ) )
              | ~ m1_subset_1(X3,sK2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( k3_subset_1(sK2,sK4) != sK3
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK3)
            | r2_hidden(X3,sK4) )
          & ( ~ r2_hidden(X3,sK4)
            | ~ r2_hidden(X3,sK3) ) )
        | ~ m1_subset_1(X3,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f26,f25])).

fof(f46,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK3)
      | r2_hidden(X3,sK4)
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

fof(f45,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK4)
      | ~ r2_hidden(X3,sK3)
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

cnf(c_15,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | r2_hidden(X0,sK3)
    | r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_823,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_24170,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) = X1
    | r2_hidden(sK1(sK2,X0,X1),X1) = iProver_top
    | r2_hidden(sK1(sK2,X0,X1),sK3) = iProver_top
    | r2_hidden(sK1(sK2,X0,X1),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2977,c_823])).

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
    inference(superposition,[status(thm)],[c_7086,c_823])).

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

cnf(c_16,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_822,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17293,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
    | r2_hidden(sK1(sK3,X0,sK3),sK3) != iProver_top
    | r2_hidden(sK1(sK3,X0,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7086,c_822])).

cnf(c_19,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1451,plain,
    ( ~ m1_subset_1(sK1(X0,X1,sK3),sK2)
    | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
    | ~ r2_hidden(sK1(X0,X1,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 59.21/8.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.21/8.00  
% 59.21/8.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.21/8.00  
% 59.21/8.00  ------  iProver source info
% 59.21/8.00  
% 59.21/8.00  git: date: 2020-06-30 10:37:57 +0100
% 59.21/8.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.21/8.00  git: non_committed_changes: false
% 59.21/8.00  git: last_make_outside_of_git: false
% 59.21/8.00  
% 59.21/8.00  ------ 
% 59.21/8.00  
% 59.21/8.00  ------ Input Options
% 59.21/8.00  
% 59.21/8.00  --out_options                           all
% 59.21/8.00  --tptp_safe_out                         true
% 59.21/8.00  --problem_path                          ""
% 59.21/8.00  --include_path                          ""
% 59.21/8.00  --clausifier                            res/vclausify_rel
% 59.21/8.00  --clausifier_options                    --mode clausify
% 59.21/8.00  --stdin                                 false
% 59.21/8.00  --stats_out                             all
% 59.21/8.00  
% 59.21/8.00  ------ General Options
% 59.21/8.00  
% 59.21/8.00  --fof                                   false
% 59.21/8.00  --time_out_real                         305.
% 59.21/8.00  --time_out_virtual                      -1.
% 59.21/8.00  --symbol_type_check                     false
% 59.21/8.00  --clausify_out                          false
% 59.21/8.00  --sig_cnt_out                           false
% 59.21/8.00  --trig_cnt_out                          false
% 59.21/8.00  --trig_cnt_out_tolerance                1.
% 59.21/8.00  --trig_cnt_out_sk_spl                   false
% 59.21/8.00  --abstr_cl_out                          false
% 59.21/8.00  
% 59.21/8.00  ------ Global Options
% 59.21/8.00  
% 59.21/8.00  --schedule                              default
% 59.21/8.00  --add_important_lit                     false
% 59.21/8.00  --prop_solver_per_cl                    1000
% 59.21/8.00  --min_unsat_core                        false
% 59.21/8.00  --soft_assumptions                      false
% 59.21/8.00  --soft_lemma_size                       3
% 59.21/8.00  --prop_impl_unit_size                   0
% 59.21/8.00  --prop_impl_unit                        []
% 59.21/8.00  --share_sel_clauses                     true
% 59.21/8.00  --reset_solvers                         false
% 59.21/8.00  --bc_imp_inh                            [conj_cone]
% 59.21/8.00  --conj_cone_tolerance                   3.
% 59.21/8.00  --extra_neg_conj                        none
% 59.21/8.00  --large_theory_mode                     true
% 59.21/8.00  --prolific_symb_bound                   200
% 59.21/8.00  --lt_threshold                          2000
% 59.21/8.00  --clause_weak_htbl                      true
% 59.21/8.00  --gc_record_bc_elim                     false
% 59.21/8.00  
% 59.21/8.00  ------ Preprocessing Options
% 59.21/8.00  
% 59.21/8.00  --preprocessing_flag                    true
% 59.21/8.00  --time_out_prep_mult                    0.1
% 59.21/8.00  --splitting_mode                        input
% 59.21/8.00  --splitting_grd                         true
% 59.21/8.00  --splitting_cvd                         false
% 59.21/8.00  --splitting_cvd_svl                     false
% 59.21/8.00  --splitting_nvd                         32
% 59.21/8.00  --sub_typing                            true
% 59.21/8.00  --prep_gs_sim                           true
% 59.21/8.00  --prep_unflatten                        true
% 59.21/8.00  --prep_res_sim                          true
% 59.21/8.00  --prep_upred                            true
% 59.21/8.00  --prep_sem_filter                       exhaustive
% 59.21/8.00  --prep_sem_filter_out                   false
% 59.21/8.00  --pred_elim                             true
% 59.21/8.00  --res_sim_input                         true
% 59.21/8.00  --eq_ax_congr_red                       true
% 59.21/8.00  --pure_diseq_elim                       true
% 59.21/8.00  --brand_transform                       false
% 59.21/8.00  --non_eq_to_eq                          false
% 59.21/8.00  --prep_def_merge                        true
% 59.21/8.00  --prep_def_merge_prop_impl              false
% 59.21/8.00  --prep_def_merge_mbd                    true
% 59.21/8.00  --prep_def_merge_tr_red                 false
% 59.21/8.00  --prep_def_merge_tr_cl                  false
% 59.21/8.00  --smt_preprocessing                     true
% 59.21/8.00  --smt_ac_axioms                         fast
% 59.21/8.00  --preprocessed_out                      false
% 59.21/8.00  --preprocessed_stats                    false
% 59.21/8.00  
% 59.21/8.00  ------ Abstraction refinement Options
% 59.21/8.00  
% 59.21/8.00  --abstr_ref                             []
% 59.21/8.00  --abstr_ref_prep                        false
% 59.21/8.00  --abstr_ref_until_sat                   false
% 59.21/8.00  --abstr_ref_sig_restrict                funpre
% 59.21/8.00  --abstr_ref_af_restrict_to_split_sk     false
% 59.21/8.00  --abstr_ref_under                       []
% 59.21/8.00  
% 59.21/8.00  ------ SAT Options
% 59.21/8.00  
% 59.21/8.00  --sat_mode                              false
% 59.21/8.00  --sat_fm_restart_options                ""
% 59.21/8.00  --sat_gr_def                            false
% 59.21/8.00  --sat_epr_types                         true
% 59.21/8.00  --sat_non_cyclic_types                  false
% 59.21/8.00  --sat_finite_models                     false
% 59.21/8.00  --sat_fm_lemmas                         false
% 59.21/8.00  --sat_fm_prep                           false
% 59.21/8.00  --sat_fm_uc_incr                        true
% 59.21/8.00  --sat_out_model                         small
% 59.21/8.00  --sat_out_clauses                       false
% 59.21/8.00  
% 59.21/8.00  ------ QBF Options
% 59.21/8.00  
% 59.21/8.00  --qbf_mode                              false
% 59.21/8.00  --qbf_elim_univ                         false
% 59.21/8.00  --qbf_dom_inst                          none
% 59.21/8.00  --qbf_dom_pre_inst                      false
% 59.21/8.00  --qbf_sk_in                             false
% 59.21/8.00  --qbf_pred_elim                         true
% 59.21/8.00  --qbf_split                             512
% 59.21/8.00  
% 59.21/8.00  ------ BMC1 Options
% 59.21/8.00  
% 59.21/8.00  --bmc1_incremental                      false
% 59.21/8.00  --bmc1_axioms                           reachable_all
% 59.21/8.00  --bmc1_min_bound                        0
% 59.21/8.00  --bmc1_max_bound                        -1
% 59.21/8.00  --bmc1_max_bound_default                -1
% 59.21/8.00  --bmc1_symbol_reachability              true
% 59.21/8.00  --bmc1_property_lemmas                  false
% 59.21/8.00  --bmc1_k_induction                      false
% 59.21/8.00  --bmc1_non_equiv_states                 false
% 59.21/8.00  --bmc1_deadlock                         false
% 59.21/8.00  --bmc1_ucm                              false
% 59.21/8.00  --bmc1_add_unsat_core                   none
% 59.21/8.00  --bmc1_unsat_core_children              false
% 59.21/8.00  --bmc1_unsat_core_extrapolate_axioms    false
% 59.21/8.00  --bmc1_out_stat                         full
% 59.21/8.00  --bmc1_ground_init                      false
% 59.21/8.00  --bmc1_pre_inst_next_state              false
% 59.21/8.00  --bmc1_pre_inst_state                   false
% 59.21/8.00  --bmc1_pre_inst_reach_state             false
% 59.21/8.00  --bmc1_out_unsat_core                   false
% 59.21/8.00  --bmc1_aig_witness_out                  false
% 59.21/8.00  --bmc1_verbose                          false
% 59.21/8.00  --bmc1_dump_clauses_tptp                false
% 59.21/8.00  --bmc1_dump_unsat_core_tptp             false
% 59.21/8.00  --bmc1_dump_file                        -
% 59.21/8.00  --bmc1_ucm_expand_uc_limit              128
% 59.21/8.00  --bmc1_ucm_n_expand_iterations          6
% 59.21/8.00  --bmc1_ucm_extend_mode                  1
% 59.21/8.00  --bmc1_ucm_init_mode                    2
% 59.21/8.00  --bmc1_ucm_cone_mode                    none
% 59.21/8.00  --bmc1_ucm_reduced_relation_type        0
% 59.21/8.00  --bmc1_ucm_relax_model                  4
% 59.21/8.00  --bmc1_ucm_full_tr_after_sat            true
% 59.21/8.00  --bmc1_ucm_expand_neg_assumptions       false
% 59.21/8.00  --bmc1_ucm_layered_model                none
% 59.21/8.00  --bmc1_ucm_max_lemma_size               10
% 59.21/8.00  
% 59.21/8.00  ------ AIG Options
% 59.21/8.00  
% 59.21/8.00  --aig_mode                              false
% 59.21/8.00  
% 59.21/8.00  ------ Instantiation Options
% 59.21/8.00  
% 59.21/8.00  --instantiation_flag                    true
% 59.21/8.00  --inst_sos_flag                         false
% 59.21/8.00  --inst_sos_phase                        true
% 59.21/8.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.21/8.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.21/8.00  --inst_lit_sel_side                     num_symb
% 59.21/8.00  --inst_solver_per_active                1400
% 59.21/8.00  --inst_solver_calls_frac                1.
% 59.21/8.00  --inst_passive_queue_type               priority_queues
% 59.21/8.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.21/8.00  --inst_passive_queues_freq              [25;2]
% 59.21/8.00  --inst_dismatching                      true
% 59.21/8.00  --inst_eager_unprocessed_to_passive     true
% 59.21/8.00  --inst_prop_sim_given                   true
% 59.21/8.00  --inst_prop_sim_new                     false
% 59.21/8.00  --inst_subs_new                         false
% 59.21/8.00  --inst_eq_res_simp                      false
% 59.21/8.00  --inst_subs_given                       false
% 59.21/8.00  --inst_orphan_elimination               true
% 59.21/8.00  --inst_learning_loop_flag               true
% 59.21/8.00  --inst_learning_start                   3000
% 59.21/8.00  --inst_learning_factor                  2
% 59.21/8.00  --inst_start_prop_sim_after_learn       3
% 59.21/8.00  --inst_sel_renew                        solver
% 59.21/8.00  --inst_lit_activity_flag                true
% 59.21/8.00  --inst_restr_to_given                   false
% 59.21/8.00  --inst_activity_threshold               500
% 59.21/8.00  --inst_out_proof                        true
% 59.21/8.00  
% 59.21/8.00  ------ Resolution Options
% 59.21/8.00  
% 59.21/8.00  --resolution_flag                       true
% 59.21/8.00  --res_lit_sel                           adaptive
% 59.21/8.00  --res_lit_sel_side                      none
% 59.21/8.00  --res_ordering                          kbo
% 59.21/8.00  --res_to_prop_solver                    active
% 59.21/8.00  --res_prop_simpl_new                    false
% 59.21/8.00  --res_prop_simpl_given                  true
% 59.21/8.00  --res_passive_queue_type                priority_queues
% 59.21/8.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.21/8.00  --res_passive_queues_freq               [15;5]
% 59.21/8.00  --res_forward_subs                      full
% 59.21/8.00  --res_backward_subs                     full
% 59.21/8.00  --res_forward_subs_resolution           true
% 59.21/8.00  --res_backward_subs_resolution          true
% 59.21/8.00  --res_orphan_elimination                true
% 59.21/8.00  --res_time_limit                        2.
% 59.21/8.00  --res_out_proof                         true
% 59.21/8.00  
% 59.21/8.00  ------ Superposition Options
% 59.21/8.00  
% 59.21/8.00  --superposition_flag                    true
% 59.21/8.00  --sup_passive_queue_type                priority_queues
% 59.21/8.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.21/8.00  --sup_passive_queues_freq               [8;1;4]
% 59.21/8.00  --demod_completeness_check              fast
% 59.21/8.00  --demod_use_ground                      true
% 59.21/8.00  --sup_to_prop_solver                    passive
% 59.21/8.00  --sup_prop_simpl_new                    true
% 59.21/8.00  --sup_prop_simpl_given                  true
% 59.21/8.00  --sup_fun_splitting                     false
% 59.21/8.00  --sup_smt_interval                      50000
% 59.21/8.00  
% 59.21/8.00  ------ Superposition Simplification Setup
% 59.21/8.00  
% 59.21/8.00  --sup_indices_passive                   []
% 59.21/8.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.21/8.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.21/8.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.21/8.00  --sup_full_triv                         [TrivRules;PropSubs]
% 59.21/8.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.21/8.00  --sup_full_bw                           [BwDemod]
% 59.21/8.00  --sup_immed_triv                        [TrivRules]
% 59.21/8.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.21/8.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.21/8.00  --sup_immed_bw_main                     []
% 59.21/8.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.21/8.00  --sup_input_triv                        [Unflattening;TrivRules]
% 59.21/8.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.21/8.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.21/8.00  
% 59.21/8.00  ------ Combination Options
% 59.21/8.00  
% 59.21/8.00  --comb_res_mult                         3
% 59.21/8.00  --comb_sup_mult                         2
% 59.21/8.00  --comb_inst_mult                        10
% 59.21/8.00  
% 59.21/8.00  ------ Debug Options
% 59.21/8.00  
% 59.21/8.00  --dbg_backtrace                         false
% 59.21/8.00  --dbg_dump_prop_clauses                 false
% 59.21/8.00  --dbg_dump_prop_clauses_file            -
% 59.21/8.00  --dbg_out_stat                          false
% 59.21/8.00  ------ Parsing...
% 59.21/8.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.21/8.00  
% 59.21/8.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 59.21/8.00  
% 59.21/8.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.21/8.00  
% 59.21/8.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.21/8.00  ------ Proving...
% 59.21/8.00  ------ Problem Properties 
% 59.21/8.00  
% 59.21/8.00  
% 59.21/8.00  clauses                                 19
% 59.21/8.00  conjectures                             5
% 59.21/8.00  EPR                                     7
% 59.21/8.00  Horn                                    12
% 59.21/8.00  unary                                   3
% 59.21/8.00  binary                                  6
% 59.21/8.00  lits                                    46
% 59.21/8.00  lits eq                                 5
% 59.21/8.00  fd_pure                                 0
% 59.21/8.00  fd_pseudo                               0
% 59.21/8.00  fd_cond                                 0
% 59.21/8.00  fd_pseudo_cond                          3
% 59.21/8.00  AC symbols                              0
% 59.21/8.00  
% 59.21/8.00  ------ Schedule dynamic 5 is on 
% 59.21/8.00  
% 59.21/8.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 59.21/8.00  
% 59.21/8.00  
% 59.21/8.00  ------ 
% 59.21/8.00  Current options:
% 59.21/8.00  ------ 
% 59.21/8.00  
% 59.21/8.00  ------ Input Options
% 59.21/8.00  
% 59.21/8.00  --out_options                           all
% 59.21/8.00  --tptp_safe_out                         true
% 59.21/8.00  --problem_path                          ""
% 59.21/8.00  --include_path                          ""
% 59.21/8.00  --clausifier                            res/vclausify_rel
% 59.21/8.00  --clausifier_options                    --mode clausify
% 59.21/8.00  --stdin                                 false
% 59.21/8.00  --stats_out                             all
% 59.21/8.00  
% 59.21/8.00  ------ General Options
% 59.21/8.00  
% 59.21/8.00  --fof                                   false
% 59.21/8.00  --time_out_real                         305.
% 59.21/8.00  --time_out_virtual                      -1.
% 59.21/8.00  --symbol_type_check                     false
% 59.21/8.00  --clausify_out                          false
% 59.21/8.00  --sig_cnt_out                           false
% 59.21/8.00  --trig_cnt_out                          false
% 59.21/8.00  --trig_cnt_out_tolerance                1.
% 59.21/8.00  --trig_cnt_out_sk_spl                   false
% 59.21/8.00  --abstr_cl_out                          false
% 59.21/8.00  
% 59.21/8.00  ------ Global Options
% 59.21/8.00  
% 59.21/8.00  --schedule                              default
% 59.21/8.00  --add_important_lit                     false
% 59.21/8.00  --prop_solver_per_cl                    1000
% 59.21/8.00  --min_unsat_core                        false
% 59.21/8.00  --soft_assumptions                      false
% 59.21/8.00  --soft_lemma_size                       3
% 59.21/8.00  --prop_impl_unit_size                   0
% 59.21/8.00  --prop_impl_unit                        []
% 59.21/8.00  --share_sel_clauses                     true
% 59.21/8.00  --reset_solvers                         false
% 59.21/8.00  --bc_imp_inh                            [conj_cone]
% 59.21/8.00  --conj_cone_tolerance                   3.
% 59.21/8.00  --extra_neg_conj                        none
% 59.21/8.00  --large_theory_mode                     true
% 59.21/8.00  --prolific_symb_bound                   200
% 59.21/8.00  --lt_threshold                          2000
% 59.21/8.00  --clause_weak_htbl                      true
% 59.21/8.00  --gc_record_bc_elim                     false
% 59.21/8.00  
% 59.21/8.00  ------ Preprocessing Options
% 59.21/8.00  
% 59.21/8.00  --preprocessing_flag                    true
% 59.21/8.00  --time_out_prep_mult                    0.1
% 59.21/8.00  --splitting_mode                        input
% 59.21/8.00  --splitting_grd                         true
% 59.21/8.00  --splitting_cvd                         false
% 59.21/8.00  --splitting_cvd_svl                     false
% 59.21/8.00  --splitting_nvd                         32
% 59.21/8.00  --sub_typing                            true
% 59.21/8.00  --prep_gs_sim                           true
% 59.21/8.00  --prep_unflatten                        true
% 59.21/8.00  --prep_res_sim                          true
% 59.21/8.00  --prep_upred                            true
% 59.21/8.00  --prep_sem_filter                       exhaustive
% 59.21/8.00  --prep_sem_filter_out                   false
% 59.21/8.00  --pred_elim                             true
% 59.21/8.00  --res_sim_input                         true
% 59.21/8.00  --eq_ax_congr_red                       true
% 59.21/8.00  --pure_diseq_elim                       true
% 59.21/8.00  --brand_transform                       false
% 59.21/8.00  --non_eq_to_eq                          false
% 59.21/8.00  --prep_def_merge                        true
% 59.21/8.00  --prep_def_merge_prop_impl              false
% 59.21/8.00  --prep_def_merge_mbd                    true
% 59.21/8.00  --prep_def_merge_tr_red                 false
% 59.21/8.00  --prep_def_merge_tr_cl                  false
% 59.21/8.00  --smt_preprocessing                     true
% 59.21/8.00  --smt_ac_axioms                         fast
% 59.21/8.00  --preprocessed_out                      false
% 59.21/8.00  --preprocessed_stats                    false
% 59.21/8.00  
% 59.21/8.00  ------ Abstraction refinement Options
% 59.21/8.00  
% 59.21/8.00  --abstr_ref                             []
% 59.21/8.00  --abstr_ref_prep                        false
% 59.21/8.00  --abstr_ref_until_sat                   false
% 59.21/8.00  --abstr_ref_sig_restrict                funpre
% 59.21/8.00  --abstr_ref_af_restrict_to_split_sk     false
% 59.21/8.00  --abstr_ref_under                       []
% 59.21/8.00  
% 59.21/8.00  ------ SAT Options
% 59.21/8.00  
% 59.21/8.00  --sat_mode                              false
% 59.21/8.00  --sat_fm_restart_options                ""
% 59.21/8.00  --sat_gr_def                            false
% 59.21/8.00  --sat_epr_types                         true
% 59.21/8.00  --sat_non_cyclic_types                  false
% 59.21/8.00  --sat_finite_models                     false
% 59.21/8.00  --sat_fm_lemmas                         false
% 59.21/8.00  --sat_fm_prep                           false
% 59.21/8.00  --sat_fm_uc_incr                        true
% 59.21/8.00  --sat_out_model                         small
% 59.21/8.00  --sat_out_clauses                       false
% 59.21/8.00  
% 59.21/8.00  ------ QBF Options
% 59.21/8.00  
% 59.21/8.00  --qbf_mode                              false
% 59.21/8.00  --qbf_elim_univ                         false
% 59.21/8.00  --qbf_dom_inst                          none
% 59.21/8.00  --qbf_dom_pre_inst                      false
% 59.21/8.00  --qbf_sk_in                             false
% 59.21/8.00  --qbf_pred_elim                         true
% 59.21/8.00  --qbf_split                             512
% 59.21/8.00  
% 59.21/8.00  ------ BMC1 Options
% 59.21/8.00  
% 59.21/8.00  --bmc1_incremental                      false
% 59.21/8.00  --bmc1_axioms                           reachable_all
% 59.21/8.00  --bmc1_min_bound                        0
% 59.21/8.00  --bmc1_max_bound                        -1
% 59.21/8.00  --bmc1_max_bound_default                -1
% 59.21/8.00  --bmc1_symbol_reachability              true
% 59.21/8.00  --bmc1_property_lemmas                  false
% 59.21/8.01  --bmc1_k_induction                      false
% 59.21/8.01  --bmc1_non_equiv_states                 false
% 59.21/8.01  --bmc1_deadlock                         false
% 59.21/8.01  --bmc1_ucm                              false
% 59.21/8.01  --bmc1_add_unsat_core                   none
% 59.21/8.01  --bmc1_unsat_core_children              false
% 59.21/8.01  --bmc1_unsat_core_extrapolate_axioms    false
% 59.21/8.01  --bmc1_out_stat                         full
% 59.21/8.01  --bmc1_ground_init                      false
% 59.21/8.01  --bmc1_pre_inst_next_state              false
% 59.21/8.01  --bmc1_pre_inst_state                   false
% 59.21/8.01  --bmc1_pre_inst_reach_state             false
% 59.21/8.01  --bmc1_out_unsat_core                   false
% 59.21/8.01  --bmc1_aig_witness_out                  false
% 59.21/8.01  --bmc1_verbose                          false
% 59.21/8.01  --bmc1_dump_clauses_tptp                false
% 59.21/8.01  --bmc1_dump_unsat_core_tptp             false
% 59.21/8.01  --bmc1_dump_file                        -
% 59.21/8.01  --bmc1_ucm_expand_uc_limit              128
% 59.21/8.01  --bmc1_ucm_n_expand_iterations          6
% 59.21/8.01  --bmc1_ucm_extend_mode                  1
% 59.21/8.01  --bmc1_ucm_init_mode                    2
% 59.21/8.01  --bmc1_ucm_cone_mode                    none
% 59.21/8.01  --bmc1_ucm_reduced_relation_type        0
% 59.21/8.01  --bmc1_ucm_relax_model                  4
% 59.21/8.01  --bmc1_ucm_full_tr_after_sat            true
% 59.21/8.01  --bmc1_ucm_expand_neg_assumptions       false
% 59.21/8.01  --bmc1_ucm_layered_model                none
% 59.21/8.01  --bmc1_ucm_max_lemma_size               10
% 59.21/8.01  
% 59.21/8.01  ------ AIG Options
% 59.21/8.01  
% 59.21/8.01  --aig_mode                              false
% 59.21/8.01  
% 59.21/8.01  ------ Instantiation Options
% 59.21/8.01  
% 59.21/8.01  --instantiation_flag                    true
% 59.21/8.01  --inst_sos_flag                         false
% 59.21/8.01  --inst_sos_phase                        true
% 59.21/8.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.21/8.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.21/8.01  --inst_lit_sel_side                     none
% 59.21/8.01  --inst_solver_per_active                1400
% 59.21/8.01  --inst_solver_calls_frac                1.
% 59.21/8.01  --inst_passive_queue_type               priority_queues
% 59.21/8.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.21/8.01  --inst_passive_queues_freq              [25;2]
% 59.21/8.01  --inst_dismatching                      true
% 59.21/8.01  --inst_eager_unprocessed_to_passive     true
% 59.21/8.01  --inst_prop_sim_given                   true
% 59.21/8.01  --inst_prop_sim_new                     false
% 59.21/8.01  --inst_subs_new                         false
% 59.21/8.01  --inst_eq_res_simp                      false
% 59.21/8.01  --inst_subs_given                       false
% 59.21/8.01  --inst_orphan_elimination               true
% 59.21/8.01  --inst_learning_loop_flag               true
% 59.21/8.01  --inst_learning_start                   3000
% 59.21/8.01  --inst_learning_factor                  2
% 59.21/8.01  --inst_start_prop_sim_after_learn       3
% 59.21/8.01  --inst_sel_renew                        solver
% 59.21/8.01  --inst_lit_activity_flag                true
% 59.21/8.01  --inst_restr_to_given                   false
% 59.21/8.01  --inst_activity_threshold               500
% 59.21/8.01  --inst_out_proof                        true
% 59.21/8.01  
% 59.21/8.01  ------ Resolution Options
% 59.21/8.01  
% 59.21/8.01  --resolution_flag                       false
% 59.21/8.01  --res_lit_sel                           adaptive
% 59.21/8.01  --res_lit_sel_side                      none
% 59.21/8.01  --res_ordering                          kbo
% 59.21/8.01  --res_to_prop_solver                    active
% 59.21/8.01  --res_prop_simpl_new                    false
% 59.21/8.01  --res_prop_simpl_given                  true
% 59.21/8.01  --res_passive_queue_type                priority_queues
% 59.21/8.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.21/8.01  --res_passive_queues_freq               [15;5]
% 59.21/8.01  --res_forward_subs                      full
% 59.21/8.01  --res_backward_subs                     full
% 59.21/8.01  --res_forward_subs_resolution           true
% 59.21/8.01  --res_backward_subs_resolution          true
% 59.21/8.01  --res_orphan_elimination                true
% 59.21/8.01  --res_time_limit                        2.
% 59.21/8.01  --res_out_proof                         true
% 59.21/8.01  
% 59.21/8.01  ------ Superposition Options
% 59.21/8.01  
% 59.21/8.01  --superposition_flag                    true
% 59.21/8.01  --sup_passive_queue_type                priority_queues
% 59.21/8.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.21/8.01  --sup_passive_queues_freq               [8;1;4]
% 59.21/8.01  --demod_completeness_check              fast
% 59.21/8.01  --demod_use_ground                      true
% 59.21/8.01  --sup_to_prop_solver                    passive
% 59.21/8.01  --sup_prop_simpl_new                    true
% 59.21/8.01  --sup_prop_simpl_given                  true
% 59.21/8.01  --sup_fun_splitting                     false
% 59.21/8.01  --sup_smt_interval                      50000
% 59.21/8.01  
% 59.21/8.01  ------ Superposition Simplification Setup
% 59.21/8.01  
% 59.21/8.01  --sup_indices_passive                   []
% 59.21/8.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.21/8.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.21/8.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.21/8.01  --sup_full_triv                         [TrivRules;PropSubs]
% 59.21/8.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.21/8.01  --sup_full_bw                           [BwDemod]
% 59.21/8.01  --sup_immed_triv                        [TrivRules]
% 59.21/8.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.21/8.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.21/8.01  --sup_immed_bw_main                     []
% 59.21/8.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.21/8.01  --sup_input_triv                        [Unflattening;TrivRules]
% 59.21/8.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.21/8.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.21/8.01  
% 59.21/8.01  ------ Combination Options
% 59.21/8.01  
% 59.21/8.01  --comb_res_mult                         3
% 59.21/8.01  --comb_sup_mult                         2
% 59.21/8.01  --comb_inst_mult                        10
% 59.21/8.01  
% 59.21/8.01  ------ Debug Options
% 59.21/8.01  
% 59.21/8.01  --dbg_backtrace                         false
% 59.21/8.01  --dbg_dump_prop_clauses                 false
% 59.21/8.01  --dbg_dump_prop_clauses_file            -
% 59.21/8.01  --dbg_out_stat                          false
% 59.21/8.01  
% 59.21/8.01  
% 59.21/8.01  
% 59.21/8.01  
% 59.21/8.01  ------ Proving...
% 59.21/8.01  
% 59.21/8.01  
% 59.21/8.01  % SZS status Theorem for theBenchmark.p
% 59.21/8.01  
% 59.21/8.01  % SZS output start CNFRefutation for theBenchmark.p
% 59.21/8.01  
% 59.21/8.01  fof(f2,axiom,(
% 59.21/8.01    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 59.21/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.21/8.01  
% 59.21/8.01  fof(f18,plain,(
% 59.21/8.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 59.21/8.01    inference(nnf_transformation,[],[f2])).
% 59.21/8.01  
% 59.21/8.01  fof(f19,plain,(
% 59.21/8.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 59.21/8.01    inference(flattening,[],[f18])).
% 59.21/8.01  
% 59.21/8.01  fof(f20,plain,(
% 59.21/8.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 59.21/8.01    inference(rectify,[],[f19])).
% 59.21/8.01  
% 59.21/8.01  fof(f21,plain,(
% 59.21/8.01    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 59.21/8.01    introduced(choice_axiom,[])).
% 59.21/8.01  
% 59.21/8.01  fof(f22,plain,(
% 59.21/8.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 59.21/8.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).
% 59.21/8.01  
% 59.21/8.01  fof(f33,plain,(
% 59.21/8.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 59.21/8.01    inference(cnf_transformation,[],[f22])).
% 59.21/8.01  
% 59.21/8.01  fof(f3,axiom,(
% 59.21/8.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 59.21/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.21/8.01  
% 59.21/8.01  fof(f36,plain,(
% 59.21/8.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 59.21/8.01    inference(cnf_transformation,[],[f3])).
% 59.21/8.01  
% 59.21/8.01  fof(f50,plain,(
% 59.21/8.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 59.21/8.01    inference(definition_unfolding,[],[f33,f36])).
% 59.21/8.01  
% 59.21/8.01  fof(f4,axiom,(
% 59.21/8.01    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 59.21/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.21/8.01  
% 59.21/8.01  fof(f9,plain,(
% 59.21/8.01    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 59.21/8.01    inference(ennf_transformation,[],[f4])).
% 59.21/8.01  
% 59.21/8.01  fof(f23,plain,(
% 59.21/8.01    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 59.21/8.01    inference(nnf_transformation,[],[f9])).
% 59.21/8.01  
% 59.21/8.01  fof(f38,plain,(
% 59.21/8.01    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 59.21/8.01    inference(cnf_transformation,[],[f23])).
% 59.21/8.01  
% 59.21/8.01  fof(f1,axiom,(
% 59.21/8.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 59.21/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.21/8.01  
% 59.21/8.01  fof(f14,plain,(
% 59.21/8.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 59.21/8.01    inference(nnf_transformation,[],[f1])).
% 59.21/8.01  
% 59.21/8.01  fof(f15,plain,(
% 59.21/8.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 59.21/8.01    inference(rectify,[],[f14])).
% 59.21/8.01  
% 59.21/8.01  fof(f16,plain,(
% 59.21/8.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 59.21/8.01    introduced(choice_axiom,[])).
% 59.21/8.01  
% 59.21/8.01  fof(f17,plain,(
% 59.21/8.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 59.21/8.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 59.21/8.01  
% 59.21/8.01  fof(f28,plain,(
% 59.21/8.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 59.21/8.01    inference(cnf_transformation,[],[f17])).
% 59.21/8.01  
% 59.21/8.01  fof(f7,conjecture,(
% 59.21/8.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 59.21/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.21/8.01  
% 59.21/8.01  fof(f8,negated_conjecture,(
% 59.21/8.01    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 59.21/8.01    inference(negated_conjecture,[],[f7])).
% 59.21/8.01  
% 59.21/8.01  fof(f12,plain,(
% 59.21/8.01    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 59.21/8.01    inference(ennf_transformation,[],[f8])).
% 59.21/8.01  
% 59.21/8.01  fof(f13,plain,(
% 59.21/8.01    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 59.21/8.01    inference(flattening,[],[f12])).
% 59.21/8.01  
% 59.21/8.01  fof(f24,plain,(
% 59.21/8.01    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((r2_hidden(X3,X1) | r2_hidden(X3,X2)) & (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 59.21/8.01    inference(nnf_transformation,[],[f13])).
% 59.21/8.01  
% 59.21/8.01  fof(f26,plain,(
% 59.21/8.01    ( ! [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((r2_hidden(X3,X1) | r2_hidden(X3,X2)) & (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k3_subset_1(X0,sK4) != X1 & ! [X3] : (((r2_hidden(X3,X1) | r2_hidden(X3,sK4)) & (~r2_hidden(X3,sK4) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(sK4,k1_zfmisc_1(X0)))) )),
% 59.21/8.01    introduced(choice_axiom,[])).
% 59.21/8.01  
% 59.21/8.01  fof(f25,plain,(
% 59.21/8.01    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((r2_hidden(X3,X1) | r2_hidden(X3,X2)) & (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k3_subset_1(sK2,X2) != sK3 & ! [X3] : (((r2_hidden(X3,sK3) | r2_hidden(X3,X2)) & (~r2_hidden(X3,X2) | ~r2_hidden(X3,sK3))) | ~m1_subset_1(X3,sK2)) & m1_subset_1(X2,k1_zfmisc_1(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(sK2)))),
% 59.21/8.01    introduced(choice_axiom,[])).
% 59.21/8.01  
% 59.21/8.01  fof(f27,plain,(
% 59.21/8.01    (k3_subset_1(sK2,sK4) != sK3 & ! [X3] : (((r2_hidden(X3,sK3) | r2_hidden(X3,sK4)) & (~r2_hidden(X3,sK4) | ~r2_hidden(X3,sK3))) | ~m1_subset_1(X3,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 59.21/8.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f26,f25])).
% 59.21/8.01  
% 59.21/8.01  fof(f46,plain,(
% 59.21/8.01    ( ! [X3] : (r2_hidden(X3,sK3) | r2_hidden(X3,sK4) | ~m1_subset_1(X3,sK2)) )),
% 59.21/8.01    inference(cnf_transformation,[],[f27])).
% 59.21/8.01  
% 59.21/8.01  fof(f34,plain,(
% 59.21/8.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 59.21/8.01    inference(cnf_transformation,[],[f22])).
% 59.21/8.01  
% 59.21/8.01  fof(f49,plain,(
% 59.21/8.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 59.21/8.01    inference(definition_unfolding,[],[f34,f36])).
% 59.21/8.01  
% 59.21/8.01  fof(f43,plain,(
% 59.21/8.01    m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 59.21/8.01    inference(cnf_transformation,[],[f27])).
% 59.21/8.01  
% 59.21/8.01  fof(f5,axiom,(
% 59.21/8.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 59.21/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.21/8.01  
% 59.21/8.01  fof(f10,plain,(
% 59.21/8.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 59.21/8.01    inference(ennf_transformation,[],[f5])).
% 59.21/8.01  
% 59.21/8.01  fof(f41,plain,(
% 59.21/8.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 59.21/8.01    inference(cnf_transformation,[],[f10])).
% 59.21/8.01  
% 59.21/8.01  fof(f54,plain,(
% 59.21/8.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 59.21/8.01    inference(definition_unfolding,[],[f41,f36])).
% 59.21/8.01  
% 59.21/8.01  fof(f44,plain,(
% 59.21/8.01    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 59.21/8.01    inference(cnf_transformation,[],[f27])).
% 59.21/8.01  
% 59.21/8.01  fof(f6,axiom,(
% 59.21/8.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 59.21/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.21/8.01  
% 59.21/8.01  fof(f11,plain,(
% 59.21/8.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 59.21/8.01    inference(ennf_transformation,[],[f6])).
% 59.21/8.01  
% 59.21/8.01  fof(f42,plain,(
% 59.21/8.01    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 59.21/8.01    inference(cnf_transformation,[],[f11])).
% 59.21/8.01  
% 59.21/8.01  fof(f35,plain,(
% 59.21/8.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 59.21/8.01    inference(cnf_transformation,[],[f22])).
% 59.21/8.01  
% 59.21/8.01  fof(f48,plain,(
% 59.21/8.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 59.21/8.01    inference(definition_unfolding,[],[f35,f36])).
% 59.21/8.01  
% 59.21/8.01  fof(f45,plain,(
% 59.21/8.01    ( ! [X3] : (~r2_hidden(X3,sK4) | ~r2_hidden(X3,sK3) | ~m1_subset_1(X3,sK2)) )),
% 59.21/8.01    inference(cnf_transformation,[],[f27])).
% 59.21/8.01  
% 59.21/8.01  fof(f31,plain,(
% 59.21/8.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 59.21/8.01    inference(cnf_transformation,[],[f22])).
% 59.21/8.01  
% 59.21/8.01  fof(f52,plain,(
% 59.21/8.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 59.21/8.01    inference(definition_unfolding,[],[f31,f36])).
% 59.21/8.01  
% 59.21/8.01  fof(f56,plain,(
% 59.21/8.01    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 59.21/8.01    inference(equality_resolution,[],[f52])).
% 59.21/8.01  
% 59.21/8.01  fof(f32,plain,(
% 59.21/8.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 59.21/8.01    inference(cnf_transformation,[],[f22])).
% 59.21/8.01  
% 59.21/8.01  fof(f51,plain,(
% 59.21/8.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 59.21/8.01    inference(definition_unfolding,[],[f32,f36])).
% 59.21/8.01  
% 59.21/8.01  fof(f55,plain,(
% 59.21/8.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 59.21/8.01    inference(equality_resolution,[],[f51])).
% 59.21/8.01  
% 59.21/8.01  fof(f47,plain,(
% 59.21/8.01    k3_subset_1(sK2,sK4) != sK3),
% 59.21/8.01    inference(cnf_transformation,[],[f27])).
% 59.21/8.01  
% 59.21/8.01  cnf(c_4,plain,
% 59.21/8.01      ( r2_hidden(sK1(X0,X1,X2),X0)
% 59.21/8.01      | r2_hidden(sK1(X0,X1,X2),X2)
% 59.21/8.01      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 59.21/8.01      inference(cnf_transformation,[],[f50]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_832,plain,
% 59.21/8.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 59.21/8.01      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_10,plain,
% 59.21/8.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 59.21/8.01      inference(cnf_transformation,[],[f38]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_1,plain,
% 59.21/8.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 59.21/8.01      inference(cnf_transformation,[],[f28]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_103,plain,
% 59.21/8.01      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 59.21/8.01      inference(global_propositional_subsumption,
% 59.21/8.01                [status(thm)],
% 59.21/8.01                [c_10,c_1]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_104,plain,
% 59.21/8.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 59.21/8.01      inference(renaming,[status(thm)],[c_103]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_819,plain,
% 59.21/8.01      ( m1_subset_1(X0,X1) = iProver_top
% 59.21/8.01      | r2_hidden(X0,X1) != iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_104]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_2977,plain,
% 59.21/8.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 59.21/8.01      | m1_subset_1(sK1(X0,X1,X2),X0) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_832,c_819]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_15,negated_conjecture,
% 59.21/8.01      ( ~ m1_subset_1(X0,sK2) | r2_hidden(X0,sK3) | r2_hidden(X0,sK4) ),
% 59.21/8.01      inference(cnf_transformation,[],[f46]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_823,plain,
% 59.21/8.01      ( m1_subset_1(X0,sK2) != iProver_top
% 59.21/8.01      | r2_hidden(X0,sK3) = iProver_top
% 59.21/8.01      | r2_hidden(X0,sK4) = iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_24170,plain,
% 59.21/8.01      ( k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) = X1
% 59.21/8.01      | r2_hidden(sK1(sK2,X0,X1),X1) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK2,X0,X1),sK3) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK2,X0,X1),sK4) = iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_2977,c_823]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_3,plain,
% 59.21/8.01      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 59.21/8.01      | r2_hidden(sK1(X0,X1,X2),X2)
% 59.21/8.01      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 59.21/8.01      inference(cnf_transformation,[],[f49]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_833,plain,
% 59.21/8.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 59.21/8.01      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_24847,plain,
% 59.21/8.01      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = X0
% 59.21/8.01      | r2_hidden(sK1(sK2,sK3,X0),X0) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK2,sK3,X0),sK4) = iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_24170,c_833]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_18,negated_conjecture,
% 59.21/8.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
% 59.21/8.01      inference(cnf_transformation,[],[f43]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_820,plain,
% 59.21/8.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_12,plain,
% 59.21/8.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 59.21/8.01      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 59.21/8.01      inference(cnf_transformation,[],[f54]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_825,plain,
% 59.21/8.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 59.21/8.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_1566,plain,
% 59.21/8.01      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = k3_subset_1(sK2,sK3) ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_820,c_825]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_24991,plain,
% 59.21/8.01      ( k3_subset_1(sK2,sK3) = X0
% 59.21/8.01      | r2_hidden(sK1(sK2,sK3,X0),X0) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK2,sK3,X0),sK4) = iProver_top ),
% 59.21/8.01      inference(demodulation,[status(thm)],[c_24847,c_1566]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_17,negated_conjecture,
% 59.21/8.01      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 59.21/8.01      inference(cnf_transformation,[],[f44]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_821,plain,
% 59.21/8.01      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_13,plain,
% 59.21/8.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 59.21/8.01      | ~ r2_hidden(X2,X0)
% 59.21/8.01      | r2_hidden(X2,X1) ),
% 59.21/8.01      inference(cnf_transformation,[],[f42]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_824,plain,
% 59.21/8.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 59.21/8.01      | r2_hidden(X2,X0) != iProver_top
% 59.21/8.01      | r2_hidden(X2,X1) = iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_1250,plain,
% 59.21/8.01      ( r2_hidden(X0,sK4) != iProver_top
% 59.21/8.01      | r2_hidden(X0,sK2) = iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_821,c_824]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_25226,plain,
% 59.21/8.01      ( k3_subset_1(sK2,sK3) = X0
% 59.21/8.01      | r2_hidden(sK1(sK2,sK3,X0),X0) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK2,sK3,X0),sK2) = iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_24991,c_1250]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_25390,plain,
% 59.21/8.01      ( k3_subset_1(sK2,sK3) = sK4
% 59.21/8.01      | r2_hidden(sK1(sK2,sK3,sK4),sK2) = iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_25226,c_1250]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_2,plain,
% 59.21/8.01      ( ~ r2_hidden(sK1(X0,X1,X2),X0)
% 59.21/8.01      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 59.21/8.01      | r2_hidden(sK1(X0,X1,X2),X1)
% 59.21/8.01      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 59.21/8.01      inference(cnf_transformation,[],[f48]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_834,plain,
% 59.21/8.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 59.21/8.01      | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_26000,plain,
% 59.21/8.01      ( k3_subset_1(sK2,sK3) = sK4
% 59.21/8.01      | k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = sK4
% 59.21/8.01      | r2_hidden(sK1(sK2,sK3,sK4),sK3) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK2,sK3,sK4),sK4) != iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_25390,c_834]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_26005,plain,
% 59.21/8.01      ( k3_subset_1(sK2,sK3) = sK4
% 59.21/8.01      | r2_hidden(sK1(sK2,sK3,sK4),sK3) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK2,sK3,sK4),sK4) != iProver_top ),
% 59.21/8.01      inference(demodulation,[status(thm)],[c_26000,c_1566]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_25245,plain,
% 59.21/8.01      ( k3_subset_1(sK2,sK3) = sK4
% 59.21/8.01      | r2_hidden(sK1(sK2,sK3,sK4),sK4) = iProver_top
% 59.21/8.01      | iProver_top != iProver_top ),
% 59.21/8.01      inference(equality_factoring,[status(thm)],[c_24991]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_25247,plain,
% 59.21/8.01      ( k3_subset_1(sK2,sK3) = sK4
% 59.21/8.01      | r2_hidden(sK1(sK2,sK3,sK4),sK4) = iProver_top ),
% 59.21/8.01      inference(equality_resolution_simp,[status(thm)],[c_25245]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_27300,plain,
% 59.21/8.01      ( r2_hidden(sK1(sK2,sK3,sK4),sK3) = iProver_top
% 59.21/8.01      | k3_subset_1(sK2,sK3) = sK4 ),
% 59.21/8.01      inference(global_propositional_subsumption,
% 59.21/8.01                [status(thm)],
% 59.21/8.01                [c_26005,c_25247]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_27301,plain,
% 59.21/8.01      ( k3_subset_1(sK2,sK3) = sK4
% 59.21/8.01      | r2_hidden(sK1(sK2,sK3,sK4),sK3) = iProver_top ),
% 59.21/8.01      inference(renaming,[status(thm)],[c_27300]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_1251,plain,
% 59.21/8.01      ( r2_hidden(X0,sK3) != iProver_top
% 59.21/8.01      | r2_hidden(X0,sK2) = iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_820,c_824]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_2974,plain,
% 59.21/8.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = sK3
% 59.21/8.01      | r2_hidden(sK1(X0,X1,sK3),X0) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(X0,X1,sK3),sK2) = iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_832,c_1251]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_6993,plain,
% 59.21/8.01      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),sK2) = iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_2974,c_1251]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_7086,plain,
% 59.21/8.01      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 59.21/8.01      | m1_subset_1(sK1(sK3,X0,sK3),sK2) = iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_6993,c_819]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_17292,plain,
% 59.21/8.01      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),sK3) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),sK4) = iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_7086,c_823]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_1987,plain,
% 59.21/8.01      ( r2_hidden(sK1(sK3,X0,X1),X1)
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,X1),sK3)
% 59.21/8.01      | k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = X1 ),
% 59.21/8.01      inference(instantiation,[status(thm)],[c_4]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_2713,plain,
% 59.21/8.01      ( r2_hidden(sK1(sK3,X0,sK3),sK3)
% 59.21/8.01      | k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3 ),
% 59.21/8.01      inference(instantiation,[status(thm)],[c_1987]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_2715,plain,
% 59.21/8.01      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),sK3) = iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_2713]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_19331,plain,
% 59.21/8.01      ( r2_hidden(sK1(sK3,X0,sK3),sK3) = iProver_top
% 59.21/8.01      | k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3 ),
% 59.21/8.01      inference(global_propositional_subsumption,
% 59.21/8.01                [status(thm)],
% 59.21/8.01                [c_17292,c_2715]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_19332,plain,
% 59.21/8.01      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),sK3) = iProver_top ),
% 59.21/8.01      inference(renaming,[status(thm)],[c_19331]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_19339,plain,
% 59.21/8.01      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),X0) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),sK3) != iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_19332,c_834]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_19346,plain,
% 59.21/8.01      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),X0) = iProver_top ),
% 59.21/8.01      inference(forward_subsumption_resolution,
% 59.21/8.01                [status(thm)],
% 59.21/8.01                [c_19339,c_19332]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_16,negated_conjecture,
% 59.21/8.01      ( ~ m1_subset_1(X0,sK2)
% 59.21/8.01      | ~ r2_hidden(X0,sK3)
% 59.21/8.01      | ~ r2_hidden(X0,sK4) ),
% 59.21/8.01      inference(cnf_transformation,[],[f45]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_822,plain,
% 59.21/8.01      ( m1_subset_1(X0,sK2) != iProver_top
% 59.21/8.01      | r2_hidden(X0,sK3) != iProver_top
% 59.21/8.01      | r2_hidden(X0,sK4) != iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_17293,plain,
% 59.21/8.01      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),sK3) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),sK4) != iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_7086,c_822]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_19,plain,
% 59.21/8.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_1451,plain,
% 59.21/8.01      ( ~ m1_subset_1(sK1(X0,X1,sK3),sK2)
% 59.21/8.01      | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
% 59.21/8.01      | ~ r2_hidden(sK1(X0,X1,sK3),sK4) ),
% 59.21/8.01      inference(instantiation,[status(thm)],[c_16]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_5323,plain,
% 59.21/8.01      ( ~ m1_subset_1(sK1(sK3,X0,sK3),sK2)
% 59.21/8.01      | ~ r2_hidden(sK1(sK3,X0,sK3),sK3)
% 59.21/8.01      | ~ r2_hidden(sK1(sK3,X0,sK3),sK4) ),
% 59.21/8.01      inference(instantiation,[status(thm)],[c_1451]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_5326,plain,
% 59.21/8.01      ( m1_subset_1(sK1(sK3,X0,sK3),sK2) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),sK3) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),sK4) != iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_5323]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_2683,plain,
% 59.21/8.01      ( m1_subset_1(sK1(sK3,X0,X1),sK2)
% 59.21/8.01      | ~ r2_hidden(sK1(sK3,X0,X1),sK2) ),
% 59.21/8.01      inference(instantiation,[status(thm)],[c_104]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_7859,plain,
% 59.21/8.01      ( m1_subset_1(sK1(sK3,X0,sK3),sK2)
% 59.21/8.01      | ~ r2_hidden(sK1(sK3,X0,sK3),sK2) ),
% 59.21/8.01      inference(instantiation,[status(thm)],[c_2683]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_7863,plain,
% 59.21/8.01      ( m1_subset_1(sK1(sK3,X0,sK3),sK2) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),sK2) != iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_7859]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_3125,plain,
% 59.21/8.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
% 59.21/8.01      | ~ r2_hidden(sK1(X1,X2,sK3),X0)
% 59.21/8.01      | r2_hidden(sK1(X1,X2,sK3),sK2) ),
% 59.21/8.01      inference(instantiation,[status(thm)],[c_13]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_8974,plain,
% 59.21/8.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
% 59.21/8.01      | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
% 59.21/8.01      | r2_hidden(sK1(X0,X1,sK3),sK2) ),
% 59.21/8.01      inference(instantiation,[status(thm)],[c_3125]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_15967,plain,
% 59.21/8.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
% 59.21/8.01      | ~ r2_hidden(sK1(sK3,X0,sK3),sK3)
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),sK2) ),
% 59.21/8.01      inference(instantiation,[status(thm)],[c_8974]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_15971,plain,
% 59.21/8.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),sK3) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),sK2) = iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_15967]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_17311,plain,
% 59.21/8.01      ( r2_hidden(sK1(sK3,X0,sK3),sK3) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),sK4) != iProver_top ),
% 59.21/8.01      inference(global_propositional_subsumption,
% 59.21/8.01                [status(thm)],
% 59.21/8.01                [c_17293,c_19,c_5326,c_7863,c_15971]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_17322,plain,
% 59.21/8.01      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),sK3) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),sK4) != iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_832,c_17311]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_17340,plain,
% 59.21/8.01      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3
% 59.21/8.01      | r2_hidden(sK1(sK3,X0,sK3),sK4) != iProver_top ),
% 59.21/8.01      inference(forward_subsumption_resolution,
% 59.21/8.01                [status(thm)],
% 59.21/8.01                [c_17322,c_17311]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_21971,plain,
% 59.21/8.01      ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) = sK3 ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_19346,c_17340]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_6,plain,
% 59.21/8.01      ( ~ r2_hidden(X0,X1)
% 59.21/8.01      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 59.21/8.01      inference(cnf_transformation,[],[f56]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_830,plain,
% 59.21/8.01      ( r2_hidden(X0,X1) != iProver_top
% 59.21/8.01      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_69764,plain,
% 59.21/8.01      ( r2_hidden(X0,sK3) != iProver_top
% 59.21/8.01      | r2_hidden(X0,sK4) != iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_21971,c_830]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_72696,plain,
% 59.21/8.01      ( k3_subset_1(sK2,sK3) = sK4
% 59.21/8.01      | r2_hidden(sK1(sK2,sK3,sK4),sK4) != iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_27301,c_69764]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_80629,plain,
% 59.21/8.01      ( k3_subset_1(sK2,sK3) = sK4 ),
% 59.21/8.01      inference(global_propositional_subsumption,
% 59.21/8.01                [status(thm)],
% 59.21/8.01                [c_72696,c_25247]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_80692,plain,
% 59.21/8.01      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = sK4 ),
% 59.21/8.01      inference(demodulation,[status(thm)],[c_80629,c_1566]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_5,plain,
% 59.21/8.01      ( ~ r2_hidden(X0,X1)
% 59.21/8.01      | r2_hidden(X0,X2)
% 59.21/8.01      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 59.21/8.01      inference(cnf_transformation,[],[f55]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_831,plain,
% 59.21/8.01      ( r2_hidden(X0,X1) != iProver_top
% 59.21/8.01      | r2_hidden(X0,X2) = iProver_top
% 59.21/8.01      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_3090,plain,
% 59.21/8.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X3
% 59.21/8.01      | r2_hidden(sK1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X1) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X3) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X2) = iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_831,c_833]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_32888,plain,
% 59.21/8.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X2
% 59.21/8.01      | r2_hidden(sK1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X2) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X1) = iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_832,c_3090]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_231331,plain,
% 59.21/8.01      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)))) = X0
% 59.21/8.01      | r2_hidden(sK1(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)),X0),sK3) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK2,sK4,X0),X0) = iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_80692,c_32888]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_1565,plain,
% 59.21/8.01      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) = k3_subset_1(sK2,sK4) ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_821,c_825]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_232184,plain,
% 59.21/8.01      ( k3_subset_1(sK2,sK4) = X0
% 59.21/8.01      | r2_hidden(sK1(sK2,sK4,X0),X0) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK2,sK4,X0),sK3) = iProver_top ),
% 59.21/8.01      inference(light_normalisation,
% 59.21/8.01                [status(thm)],
% 59.21/8.01                [c_231331,c_1565,c_80692]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_233708,plain,
% 59.21/8.01      ( k3_subset_1(sK2,sK4) = X0
% 59.21/8.01      | r2_hidden(sK1(sK2,sK4,X0),X0) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK2,sK4,X0),sK2) = iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_232184,c_1251]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_234063,plain,
% 59.21/8.01      ( k3_subset_1(sK2,sK4) = sK3
% 59.21/8.01      | r2_hidden(sK1(sK2,sK4,sK3),sK2) = iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_233708,c_1251]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_14,negated_conjecture,
% 59.21/8.01      ( k3_subset_1(sK2,sK4) != sK3 ),
% 59.21/8.01      inference(cnf_transformation,[],[f47]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_156033,plain,
% 59.21/8.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
% 59.21/8.01      | ~ r2_hidden(sK1(X0,sK4,sK3),sK3)
% 59.21/8.01      | r2_hidden(sK1(X0,sK4,sK3),sK2) ),
% 59.21/8.01      inference(instantiation,[status(thm)],[c_8974]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_156034,plain,
% 59.21/8.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(X0,sK4,sK3),sK3) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(X0,sK4,sK3),sK2) = iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_156033]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_156036,plain,
% 59.21/8.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK2,sK4,sK3),sK3) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK2,sK4,sK3),sK2) = iProver_top ),
% 59.21/8.01      inference(instantiation,[status(thm)],[c_156034]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_233754,plain,
% 59.21/8.01      ( k3_subset_1(sK2,sK4) = sK3
% 59.21/8.01      | r2_hidden(sK1(sK2,sK4,sK3),sK3) = iProver_top
% 59.21/8.01      | iProver_top != iProver_top ),
% 59.21/8.01      inference(equality_factoring,[status(thm)],[c_232184]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_233756,plain,
% 59.21/8.01      ( k3_subset_1(sK2,sK4) = sK3
% 59.21/8.01      | r2_hidden(sK1(sK2,sK4,sK3),sK3) = iProver_top ),
% 59.21/8.01      inference(equality_resolution_simp,[status(thm)],[c_233754]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_234518,plain,
% 59.21/8.01      ( r2_hidden(sK1(sK2,sK4,sK3),sK2) = iProver_top ),
% 59.21/8.01      inference(global_propositional_subsumption,
% 59.21/8.01                [status(thm)],
% 59.21/8.01                [c_234063,c_19,c_14,c_156036,c_233756]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_234525,plain,
% 59.21/8.01      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) = sK3
% 59.21/8.01      | r2_hidden(sK1(sK2,sK4,sK3),sK3) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK2,sK4,sK3),sK4) = iProver_top ),
% 59.21/8.01      inference(superposition,[status(thm)],[c_234518,c_834]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_234534,plain,
% 59.21/8.01      ( k3_subset_1(sK2,sK4) = sK3
% 59.21/8.01      | r2_hidden(sK1(sK2,sK4,sK3),sK3) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK2,sK4,sK3),sK4) = iProver_top ),
% 59.21/8.01      inference(demodulation,[status(thm)],[c_234525,c_1565]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_12079,plain,
% 59.21/8.01      ( ~ m1_subset_1(sK1(X0,sK4,sK3),sK2)
% 59.21/8.01      | ~ r2_hidden(sK1(X0,sK4,sK3),sK3)
% 59.21/8.01      | ~ r2_hidden(sK1(X0,sK4,sK3),sK4) ),
% 59.21/8.01      inference(instantiation,[status(thm)],[c_1451]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_12084,plain,
% 59.21/8.01      ( m1_subset_1(sK1(X0,sK4,sK3),sK2) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(X0,sK4,sK3),sK3) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(X0,sK4,sK3),sK4) != iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_12079]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_12086,plain,
% 59.21/8.01      ( m1_subset_1(sK1(sK2,sK4,sK3),sK2) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK2,sK4,sK3),sK3) != iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK2,sK4,sK3),sK4) != iProver_top ),
% 59.21/8.01      inference(instantiation,[status(thm)],[c_12084]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_1587,plain,
% 59.21/8.01      ( m1_subset_1(sK1(X0,X1,sK3),sK2)
% 59.21/8.01      | ~ r2_hidden(sK1(X0,X1,sK3),sK2) ),
% 59.21/8.01      inference(instantiation,[status(thm)],[c_104]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_11595,plain,
% 59.21/8.01      ( m1_subset_1(sK1(X0,sK4,sK3),sK2)
% 59.21/8.01      | ~ r2_hidden(sK1(X0,sK4,sK3),sK2) ),
% 59.21/8.01      inference(instantiation,[status(thm)],[c_1587]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_11596,plain,
% 59.21/8.01      ( m1_subset_1(sK1(X0,sK4,sK3),sK2) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(X0,sK4,sK3),sK2) != iProver_top ),
% 59.21/8.01      inference(predicate_to_equality,[status(thm)],[c_11595]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(c_11598,plain,
% 59.21/8.01      ( m1_subset_1(sK1(sK2,sK4,sK3),sK2) = iProver_top
% 59.21/8.01      | r2_hidden(sK1(sK2,sK4,sK3),sK2) != iProver_top ),
% 59.21/8.01      inference(instantiation,[status(thm)],[c_11596]) ).
% 59.21/8.01  
% 59.21/8.01  cnf(contradiction,plain,
% 59.21/8.01      ( $false ),
% 59.21/8.01      inference(minisat,
% 59.21/8.01                [status(thm)],
% 59.21/8.01                [c_234534,c_233756,c_156036,c_12086,c_11598,c_14,c_19]) ).
% 59.21/8.01  
% 59.21/8.01  
% 59.21/8.01  % SZS output end CNFRefutation for theBenchmark.p
% 59.21/8.01  
% 59.21/8.01  ------                               Statistics
% 59.21/8.01  
% 59.21/8.01  ------ General
% 59.21/8.01  
% 59.21/8.01  abstr_ref_over_cycles:                  0
% 59.21/8.01  abstr_ref_under_cycles:                 0
% 59.21/8.01  gc_basic_clause_elim:                   0
% 59.21/8.01  forced_gc_time:                         0
% 59.21/8.01  parsing_time:                           0.008
% 59.21/8.01  unif_index_cands_time:                  0.
% 59.21/8.01  unif_index_add_time:                    0.
% 59.21/8.01  orderings_time:                         0.
% 59.21/8.01  out_proof_time:                         0.022
% 59.21/8.01  total_time:                             7.018
% 59.21/8.01  num_of_symbols:                         43
% 59.21/8.01  num_of_terms:                           256995
% 59.21/8.01  
% 59.21/8.01  ------ Preprocessing
% 59.21/8.01  
% 59.21/8.01  num_of_splits:                          0
% 59.21/8.01  num_of_split_atoms:                     0
% 59.21/8.01  num_of_reused_defs:                     0
% 59.21/8.01  num_eq_ax_congr_red:                    16
% 59.21/8.01  num_of_sem_filtered_clauses:            1
% 59.21/8.01  num_of_subtypes:                        0
% 59.21/8.01  monotx_restored_types:                  0
% 59.21/8.01  sat_num_of_epr_types:                   0
% 59.21/8.01  sat_num_of_non_cyclic_types:            0
% 59.21/8.01  sat_guarded_non_collapsed_types:        0
% 59.21/8.01  num_pure_diseq_elim:                    0
% 59.21/8.01  simp_replaced_by:                       0
% 59.21/8.01  res_preprocessed:                       72
% 59.21/8.01  prep_upred:                             0
% 59.21/8.01  prep_unflattend:                        32
% 59.21/8.01  smt_new_axioms:                         0
% 59.21/8.01  pred_elim_cands:                        3
% 59.21/8.01  pred_elim:                              0
% 59.21/8.01  pred_elim_cl:                           0
% 59.21/8.01  pred_elim_cycles:                       1
% 59.21/8.01  merged_defs:                            0
% 59.21/8.01  merged_defs_ncl:                        0
% 59.21/8.01  bin_hyper_res:                          0
% 59.21/8.01  prep_cycles:                            3
% 59.21/8.01  pred_elim_time:                         0.006
% 59.21/8.01  splitting_time:                         0.
% 59.21/8.01  sem_filter_time:                        0.
% 59.21/8.01  monotx_time:                            0.
% 59.21/8.01  subtype_inf_time:                       0.
% 59.21/8.01  
% 59.21/8.01  ------ Problem properties
% 59.21/8.01  
% 59.21/8.01  clauses:                                19
% 59.21/8.01  conjectures:                            5
% 59.21/8.01  epr:                                    7
% 59.21/8.01  horn:                                   12
% 59.21/8.01  ground:                                 3
% 59.21/8.01  unary:                                  3
% 59.21/8.01  binary:                                 6
% 59.21/8.01  lits:                                   46
% 59.21/8.01  lits_eq:                                5
% 59.21/8.01  fd_pure:                                0
% 59.21/8.01  fd_pseudo:                              0
% 59.21/8.01  fd_cond:                                0
% 59.21/8.01  fd_pseudo_cond:                         3
% 59.21/8.01  ac_symbols:                             0
% 59.21/8.01  
% 59.21/8.01  ------ Propositional Solver
% 59.21/8.01  
% 59.21/8.01  prop_solver_calls:                      62
% 59.21/8.01  prop_fast_solver_calls:                 3082
% 59.21/8.01  smt_solver_calls:                       0
% 59.21/8.01  smt_fast_solver_calls:                  0
% 59.21/8.01  prop_num_of_clauses:                    61733
% 59.21/8.01  prop_preprocess_simplified:             103692
% 59.21/8.01  prop_fo_subsumed:                       138
% 59.21/8.01  prop_solver_time:                       0.
% 59.21/8.01  smt_solver_time:                        0.
% 59.21/8.01  smt_fast_solver_time:                   0.
% 59.21/8.01  prop_fast_solver_time:                  0.
% 59.21/8.01  prop_unsat_core_time:                   0.004
% 59.21/8.01  
% 59.21/8.01  ------ QBF
% 59.21/8.01  
% 59.21/8.01  qbf_q_res:                              0
% 59.21/8.01  qbf_num_tautologies:                    0
% 59.21/8.01  qbf_prep_cycles:                        0
% 59.21/8.01  
% 59.21/8.01  ------ BMC1
% 59.21/8.01  
% 59.21/8.01  bmc1_current_bound:                     -1
% 59.21/8.01  bmc1_last_solved_bound:                 -1
% 59.21/8.01  bmc1_unsat_core_size:                   -1
% 59.21/8.01  bmc1_unsat_core_parents_size:           -1
% 59.21/8.01  bmc1_merge_next_fun:                    0
% 59.21/8.01  bmc1_unsat_core_clauses_time:           0.
% 59.21/8.01  
% 59.21/8.01  ------ Instantiation
% 59.21/8.01  
% 59.21/8.01  inst_num_of_clauses:                    1358
% 59.21/8.01  inst_num_in_passive:                    546
% 59.21/8.01  inst_num_in_active:                     2663
% 59.21/8.01  inst_num_in_unprocessed:                380
% 59.21/8.01  inst_num_of_loops:                      3459
% 59.21/8.01  inst_num_of_learning_restarts:          1
% 59.21/8.01  inst_num_moves_active_passive:          795
% 59.21/8.01  inst_lit_activity:                      0
% 59.21/8.01  inst_lit_activity_moves:                0
% 59.21/8.01  inst_num_tautologies:                   0
% 59.21/8.01  inst_num_prop_implied:                  0
% 59.21/8.01  inst_num_existing_simplified:           0
% 59.21/8.01  inst_num_eq_res_simplified:             0
% 59.21/8.01  inst_num_child_elim:                    0
% 59.21/8.01  inst_num_of_dismatching_blockings:      34980
% 59.21/8.01  inst_num_of_non_proper_insts:           15595
% 59.21/8.01  inst_num_of_duplicates:                 0
% 59.21/8.01  inst_inst_num_from_inst_to_res:         0
% 59.21/8.01  inst_dismatching_checking_time:         0.
% 59.21/8.01  
% 59.21/8.01  ------ Resolution
% 59.21/8.01  
% 59.21/8.01  res_num_of_clauses:                     26
% 59.21/8.01  res_num_in_passive:                     26
% 59.21/8.01  res_num_in_active:                      0
% 59.21/8.01  res_num_of_loops:                       75
% 59.21/8.01  res_forward_subset_subsumed:            398
% 59.21/8.01  res_backward_subset_subsumed:           4
% 59.21/8.01  res_forward_subsumed:                   1
% 59.21/8.01  res_backward_subsumed:                  0
% 59.21/8.01  res_forward_subsumption_resolution:     0
% 59.21/8.01  res_backward_subsumption_resolution:    0
% 59.21/8.01  res_clause_to_clause_subsumption:       86560
% 59.21/8.01  res_orphan_elimination:                 0
% 59.21/8.01  res_tautology_del:                      2590
% 59.21/8.01  res_num_eq_res_simplified:              0
% 59.21/8.01  res_num_sel_changes:                    0
% 59.21/8.01  res_moves_from_active_to_pass:          0
% 59.21/8.01  
% 59.21/8.01  ------ Superposition
% 59.21/8.01  
% 59.21/8.01  sup_time_total:                         0.
% 59.21/8.01  sup_time_generating:                    0.
% 59.21/8.01  sup_time_sim_full:                      0.
% 59.21/8.01  sup_time_sim_immed:                     0.
% 59.21/8.01  
% 59.21/8.01  sup_num_of_clauses:                     6718
% 59.21/8.01  sup_num_in_active:                      578
% 59.21/8.01  sup_num_in_passive:                     6140
% 59.21/8.01  sup_num_of_loops:                       690
% 59.21/8.01  sup_fw_superposition:                   4464
% 59.21/8.01  sup_bw_superposition:                   8111
% 59.21/8.01  sup_immediate_simplified:               4585
% 59.21/8.01  sup_given_eliminated:                   17
% 59.21/8.01  comparisons_done:                       0
% 59.21/8.01  comparisons_avoided:                    167
% 59.21/8.01  
% 59.21/8.01  ------ Simplifications
% 59.21/8.01  
% 59.21/8.01  
% 59.21/8.01  sim_fw_subset_subsumed:                 1258
% 59.21/8.01  sim_bw_subset_subsumed:                 75
% 59.21/8.01  sim_fw_subsumed:                        2299
% 59.21/8.01  sim_bw_subsumed:                        159
% 59.21/8.01  sim_fw_subsumption_res:                 165
% 59.21/8.01  sim_bw_subsumption_res:                 13
% 59.21/8.01  sim_tautology_del:                      383
% 59.21/8.01  sim_eq_tautology_del:                   71
% 59.21/8.01  sim_eq_res_simp:                        95
% 59.21/8.01  sim_fw_demodulated:                     340
% 59.21/8.01  sim_bw_demodulated:                     117
% 59.21/8.01  sim_light_normalised:                   1071
% 59.21/8.01  sim_joinable_taut:                      0
% 59.21/8.01  sim_joinable_simp:                      0
% 59.21/8.01  sim_ac_normalised:                      0
% 59.21/8.01  sim_smt_subsumption:                    0
% 59.21/8.01  
%------------------------------------------------------------------------------

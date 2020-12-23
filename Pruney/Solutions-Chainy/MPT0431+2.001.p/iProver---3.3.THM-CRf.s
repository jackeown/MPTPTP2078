%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:49 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 230 expanded)
%              Number of clauses        :   46 (  61 expanded)
%              Number of leaves         :   12 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  308 ( 990 expanded)
%              Number of equality atoms :   28 (  38 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v3_setfam_1(X1,X0) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                & v3_setfam_1(X2,X0) )
             => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X1,X0) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                  & v3_setfam_1(X2,X0) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X1,X0) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X2,X0) )
           => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      & v3_setfam_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      & v3_setfam_1(X1,X0) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X2,X0) )
     => ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,sK4),X0)
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0)))
        & v3_setfam_1(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v3_setfam_1(X2,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        & v3_setfam_1(X1,X0) )
   => ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK2),sK3,X2),sK2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2)))
          & v3_setfam_1(X2,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))
      & v3_setfam_1(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4),sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    & v3_setfam_1(sK4,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    & v3_setfam_1(sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f29,f28])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v3_setfam_1(X1,X0)
          | r2_hidden(X0,X1) )
        & ( ~ r2_hidden(X0,X1)
          | ~ v3_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v3_setfam_1(X1,X0)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_setfam_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    v3_setfam_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    v3_setfam_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_8300,plain,
    ( ~ r2_hidden(X0,k2_xboole_0(sK3,sK4))
    | r2_hidden(X0,sK4)
    | r2_hidden(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_8302,plain,
    ( ~ r2_hidden(sK2,k2_xboole_0(sK3,sK4))
    | r2_hidden(sK2,sK4)
    | r2_hidden(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_8300])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2098,plain,
    ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X1)
    | r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X0)
    | r1_tarski(k2_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_8,c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_974,plain,
    ( r1_tarski(sK3,k1_zfmisc_1(sK2)) ),
    inference(resolution,[status(thm)],[c_14,c_18])).

cnf(c_2022,plain,
    ( r2_hidden(X0,k1_zfmisc_1(sK2))
    | ~ r2_hidden(X0,sK3) ),
    inference(resolution,[status(thm)],[c_2,c_974])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2241,plain,
    ( ~ r2_hidden(sK0(X0,k1_zfmisc_1(sK2)),sK3)
    | r1_tarski(X0,k1_zfmisc_1(sK2)) ),
    inference(resolution,[status(thm)],[c_2022,c_0])).

cnf(c_6579,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK3,X0),k1_zfmisc_1(sK2)),X0)
    | r1_tarski(k2_xboole_0(sK3,X0),k1_zfmisc_1(sK2)) ),
    inference(resolution,[status(thm)],[c_2098,c_2241])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_972,plain,
    ( r1_tarski(sK4,k1_zfmisc_1(sK2)) ),
    inference(resolution,[status(thm)],[c_14,c_16])).

cnf(c_2020,plain,
    ( r2_hidden(X0,k1_zfmisc_1(sK2))
    | ~ r2_hidden(X0,sK4) ),
    inference(resolution,[status(thm)],[c_2,c_972])).

cnf(c_2227,plain,
    ( ~ r2_hidden(sK0(X0,k1_zfmisc_1(sK2)),sK4)
    | r1_tarski(X0,k1_zfmisc_1(sK2)) ),
    inference(resolution,[status(thm)],[c_2020,c_0])).

cnf(c_6947,plain,
    ( r1_tarski(k2_xboole_0(sK3,sK4),k1_zfmisc_1(sK2)) ),
    inference(resolution,[status(thm)],[c_6579,c_2227])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_920,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(X0,k1_zfmisc_1(X1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1894,plain,
    ( m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ r1_tarski(k2_xboole_0(sK3,sK4),k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_920])).

cnf(c_1896,plain,
    ( m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ r1_tarski(k2_xboole_0(sK3,sK4),k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1894])).

cnf(c_11,plain,
    ( v3_setfam_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1403,plain,
    ( v3_setfam_1(k2_xboole_0(sK3,sK4),X0)
    | ~ m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | r2_hidden(X0,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1405,plain,
    ( v3_setfam_1(k2_xboole_0(sK3,sK4),sK2)
    | ~ m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | r2_hidden(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1403])).

cnf(c_12,plain,
    ( ~ v3_setfam_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1377,plain,
    ( ~ v3_setfam_1(sK3,sK2)
    | ~ r2_hidden(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_12,c_18])).

cnf(c_1375,plain,
    ( ~ v3_setfam_1(sK4,sK2)
    | ~ r2_hidden(sK2,sK4) ),
    inference(resolution,[status(thm)],[c_12,c_16])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_130,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_131,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_130])).

cnf(c_167,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_131])).

cnf(c_264,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_265,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_264])).

cnf(c_300,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_167,c_265])).

cnf(c_1280,plain,
    ( ~ r1_tarski(sK4,k1_zfmisc_1(sK2))
    | ~ r1_tarski(sK3,k1_zfmisc_1(sK2))
    | k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_356,plain,
    ( ~ v3_setfam_1(X0,X1)
    | v3_setfam_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1215,plain,
    ( ~ v3_setfam_1(X0,X1)
    | v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4),sK2)
    | k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_1279,plain,
    ( v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4),sK2)
    | ~ v3_setfam_1(k2_xboole_0(sK3,sK4),X0)
    | k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4) != k2_xboole_0(sK3,sK4)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1215])).

cnf(c_1282,plain,
    ( v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4),sK2)
    | ~ v3_setfam_1(k2_xboole_0(sK3,sK4),sK2)
    | k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4) != k2_xboole_0(sK3,sK4)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1279])).

cnf(c_350,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_363,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_15,negated_conjecture,
    ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,negated_conjecture,
    ( v3_setfam_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_19,negated_conjecture,
    ( v3_setfam_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8302,c_6947,c_1896,c_1405,c_1377,c_1375,c_1280,c_1282,c_974,c_972,c_363,c_15,c_17,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:57:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.52/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/0.98  
% 3.52/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.52/0.98  
% 3.52/0.98  ------  iProver source info
% 3.52/0.98  
% 3.52/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.52/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.52/0.98  git: non_committed_changes: false
% 3.52/0.98  git: last_make_outside_of_git: false
% 3.52/0.98  
% 3.52/0.98  ------ 
% 3.52/0.98  ------ Parsing...
% 3.52/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.52/0.98  
% 3.52/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.52/0.98  
% 3.52/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.52/0.98  
% 3.52/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.52/0.98  ------ Proving...
% 3.52/0.98  ------ Problem Properties 
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  clauses                                 19
% 3.52/0.98  conjectures                             5
% 3.52/0.98  EPR                                     3
% 3.52/0.98  Horn                                    15
% 3.52/0.98  unary                                   5
% 3.52/0.98  binary                                  6
% 3.52/0.98  lits                                    42
% 3.52/0.98  lits eq                                 4
% 3.52/0.98  fd_pure                                 0
% 3.52/0.98  fd_pseudo                               0
% 3.52/0.98  fd_cond                                 0
% 3.52/0.98  fd_pseudo_cond                          3
% 3.52/0.98  AC symbols                              0
% 3.52/0.98  
% 3.52/0.98  ------ Input Options Time Limit: Unbounded
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  ------ 
% 3.52/0.98  Current options:
% 3.52/0.98  ------ 
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  ------ Proving...
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  % SZS status Theorem for theBenchmark.p
% 3.52/0.98  
% 3.52/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.52/0.98  
% 3.52/0.98  fof(f2,axiom,(
% 3.52/0.98    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f21,plain,(
% 3.52/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.52/0.98    inference(nnf_transformation,[],[f2])).
% 3.52/0.98  
% 3.52/0.98  fof(f22,plain,(
% 3.52/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.52/0.98    inference(flattening,[],[f21])).
% 3.52/0.98  
% 3.52/0.98  fof(f23,plain,(
% 3.52/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.52/0.98    inference(rectify,[],[f22])).
% 3.52/0.98  
% 3.52/0.98  fof(f24,plain,(
% 3.52/0.98    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.52/0.98    introduced(choice_axiom,[])).
% 3.52/0.98  
% 3.52/0.98  fof(f25,plain,(
% 3.52/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.52/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).
% 3.52/0.98  
% 3.52/0.98  fof(f34,plain,(
% 3.52/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.52/0.98    inference(cnf_transformation,[],[f25])).
% 3.52/0.98  
% 3.52/0.98  fof(f53,plain,(
% 3.52/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 3.52/0.98    inference(equality_resolution,[],[f34])).
% 3.52/0.98  
% 3.52/0.98  fof(f1,axiom,(
% 3.52/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f10,plain,(
% 3.52/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.52/0.98    inference(ennf_transformation,[],[f1])).
% 3.52/0.98  
% 3.52/0.98  fof(f17,plain,(
% 3.52/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.52/0.98    inference(nnf_transformation,[],[f10])).
% 3.52/0.98  
% 3.52/0.98  fof(f18,plain,(
% 3.52/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.52/0.98    inference(rectify,[],[f17])).
% 3.52/0.98  
% 3.52/0.98  fof(f19,plain,(
% 3.52/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.52/0.98    introduced(choice_axiom,[])).
% 3.52/0.98  
% 3.52/0.98  fof(f20,plain,(
% 3.52/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.52/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 3.52/0.98  
% 3.52/0.98  fof(f32,plain,(
% 3.52/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f20])).
% 3.52/0.98  
% 3.52/0.98  fof(f31,plain,(
% 3.52/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f20])).
% 3.52/0.98  
% 3.52/0.98  fof(f6,axiom,(
% 3.52/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f27,plain,(
% 3.52/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.52/0.98    inference(nnf_transformation,[],[f6])).
% 3.52/0.98  
% 3.52/0.98  fof(f44,plain,(
% 3.52/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.52/0.98    inference(cnf_transformation,[],[f27])).
% 3.52/0.98  
% 3.52/0.98  fof(f7,conjecture,(
% 3.52/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0))))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f8,negated_conjecture,(
% 3.52/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0))))),
% 3.52/0.98    inference(negated_conjecture,[],[f7])).
% 3.52/0.98  
% 3.52/0.98  fof(f9,plain,(
% 3.52/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)))),
% 3.52/0.98    inference(pure_predicate_removal,[],[f8])).
% 3.52/0.98  
% 3.52/0.98  fof(f15,plain,(
% 3.52/0.98    ? [X0,X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)))),
% 3.52/0.98    inference(ennf_transformation,[],[f9])).
% 3.52/0.98  
% 3.52/0.98  fof(f16,plain,(
% 3.52/0.98    ? [X0,X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0))),
% 3.52/0.98    inference(flattening,[],[f15])).
% 3.52/0.98  
% 3.52/0.98  fof(f29,plain,(
% 3.52/0.98    ( ! [X0,X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,sK4),X0) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(sK4,X0))) )),
% 3.52/0.98    introduced(choice_axiom,[])).
% 3.52/0.98  
% 3.52/0.98  fof(f28,plain,(
% 3.52/0.98    ? [X0,X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK2),sK3,X2),sK2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2))) & v3_setfam_1(X2,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) & v3_setfam_1(sK3,sK2))),
% 3.52/0.98    introduced(choice_axiom,[])).
% 3.52/0.98  
% 3.52/0.98  fof(f30,plain,(
% 3.52/0.98    (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4),sK2) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) & v3_setfam_1(sK4,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) & v3_setfam_1(sK3,sK2)),
% 3.52/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f29,f28])).
% 3.52/0.98  
% 3.52/0.98  fof(f47,plain,(
% 3.52/0.98    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 3.52/0.98    inference(cnf_transformation,[],[f30])).
% 3.52/0.98  
% 3.52/0.98  fof(f33,plain,(
% 3.52/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f20])).
% 3.52/0.98  
% 3.52/0.98  fof(f49,plain,(
% 3.52/0.98    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 3.52/0.98    inference(cnf_transformation,[],[f30])).
% 3.52/0.98  
% 3.52/0.98  fof(f45,plain,(
% 3.52/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f27])).
% 3.52/0.98  
% 3.52/0.98  fof(f5,axiom,(
% 3.52/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f14,plain,(
% 3.52/0.98    ! [X0,X1] : ((v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.52/0.98    inference(ennf_transformation,[],[f5])).
% 3.52/0.98  
% 3.52/0.98  fof(f26,plain,(
% 3.52/0.98    ! [X0,X1] : (((v3_setfam_1(X1,X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.52/0.98    inference(nnf_transformation,[],[f14])).
% 3.52/0.98  
% 3.52/0.98  fof(f43,plain,(
% 3.52/0.98    ( ! [X0,X1] : (v3_setfam_1(X1,X0) | r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.52/0.98    inference(cnf_transformation,[],[f26])).
% 3.52/0.98  
% 3.52/0.98  fof(f42,plain,(
% 3.52/0.98    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.52/0.98    inference(cnf_transformation,[],[f26])).
% 3.52/0.98  
% 3.52/0.98  fof(f4,axiom,(
% 3.52/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.52/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f12,plain,(
% 3.52/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.52/0.98    inference(ennf_transformation,[],[f4])).
% 3.52/0.98  
% 3.52/0.98  fof(f13,plain,(
% 3.52/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.52/0.98    inference(flattening,[],[f12])).
% 3.52/0.98  
% 3.52/0.98  fof(f41,plain,(
% 3.52/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.52/0.98    inference(cnf_transformation,[],[f13])).
% 3.52/0.98  
% 3.52/0.98  fof(f50,plain,(
% 3.52/0.98    ~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4),sK2)),
% 3.52/0.98    inference(cnf_transformation,[],[f30])).
% 3.52/0.98  
% 3.52/0.98  fof(f48,plain,(
% 3.52/0.98    v3_setfam_1(sK4,sK2)),
% 3.52/0.98    inference(cnf_transformation,[],[f30])).
% 3.52/0.98  
% 3.52/0.98  fof(f46,plain,(
% 3.52/0.98    v3_setfam_1(sK3,sK2)),
% 3.52/0.98    inference(cnf_transformation,[],[f30])).
% 3.52/0.98  
% 3.52/0.98  cnf(c_8,plain,
% 3.52/0.98      ( r2_hidden(X0,X1)
% 3.52/0.98      | r2_hidden(X0,X2)
% 3.52/0.98      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.52/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_8300,plain,
% 3.52/0.98      ( ~ r2_hidden(X0,k2_xboole_0(sK3,sK4))
% 3.52/0.99      | r2_hidden(X0,sK4)
% 3.52/0.99      | r2_hidden(X0,sK3) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_8302,plain,
% 3.52/0.99      ( ~ r2_hidden(sK2,k2_xboole_0(sK3,sK4))
% 3.52/0.99      | r2_hidden(sK2,sK4)
% 3.52/0.99      | r2_hidden(sK2,sK3) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_8300]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1,plain,
% 3.52/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.52/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2098,plain,
% 3.52/0.99      ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X1)
% 3.52/0.99      | r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X0)
% 3.52/0.99      | r1_tarski(k2_xboole_0(X0,X1),X2) ),
% 3.52/0.99      inference(resolution,[status(thm)],[c_8,c_1]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2,plain,
% 3.52/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.52/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_14,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.52/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_18,negated_conjecture,
% 3.52/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 3.52/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_974,plain,
% 3.52/0.99      ( r1_tarski(sK3,k1_zfmisc_1(sK2)) ),
% 3.52/0.99      inference(resolution,[status(thm)],[c_14,c_18]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2022,plain,
% 3.52/0.99      ( r2_hidden(X0,k1_zfmisc_1(sK2)) | ~ r2_hidden(X0,sK3) ),
% 3.52/0.99      inference(resolution,[status(thm)],[c_2,c_974]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_0,plain,
% 3.52/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.52/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2241,plain,
% 3.52/0.99      ( ~ r2_hidden(sK0(X0,k1_zfmisc_1(sK2)),sK3)
% 3.52/0.99      | r1_tarski(X0,k1_zfmisc_1(sK2)) ),
% 3.52/0.99      inference(resolution,[status(thm)],[c_2022,c_0]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_6579,plain,
% 3.52/0.99      ( r2_hidden(sK0(k2_xboole_0(sK3,X0),k1_zfmisc_1(sK2)),X0)
% 3.52/0.99      | r1_tarski(k2_xboole_0(sK3,X0),k1_zfmisc_1(sK2)) ),
% 3.52/0.99      inference(resolution,[status(thm)],[c_2098,c_2241]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_16,negated_conjecture,
% 3.52/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 3.52/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_972,plain,
% 3.52/0.99      ( r1_tarski(sK4,k1_zfmisc_1(sK2)) ),
% 3.52/0.99      inference(resolution,[status(thm)],[c_14,c_16]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2020,plain,
% 3.52/0.99      ( r2_hidden(X0,k1_zfmisc_1(sK2)) | ~ r2_hidden(X0,sK4) ),
% 3.52/0.99      inference(resolution,[status(thm)],[c_2,c_972]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2227,plain,
% 3.52/0.99      ( ~ r2_hidden(sK0(X0,k1_zfmisc_1(sK2)),sK4)
% 3.52/0.99      | r1_tarski(X0,k1_zfmisc_1(sK2)) ),
% 3.52/0.99      inference(resolution,[status(thm)],[c_2020,c_0]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_6947,plain,
% 3.52/0.99      ( r1_tarski(k2_xboole_0(sK3,sK4),k1_zfmisc_1(sK2)) ),
% 3.52/0.99      inference(resolution,[status(thm)],[c_6579,c_2227]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_13,plain,
% 3.52/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.52/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_920,plain,
% 3.52/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.52/0.99      | ~ r1_tarski(X0,k1_zfmisc_1(X1)) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1894,plain,
% 3.52/0.99      ( m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(X0)))
% 3.52/0.99      | ~ r1_tarski(k2_xboole_0(sK3,sK4),k1_zfmisc_1(X0)) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_920]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1896,plain,
% 3.52/0.99      ( m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK2)))
% 3.52/0.99      | ~ r1_tarski(k2_xboole_0(sK3,sK4),k1_zfmisc_1(sK2)) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_1894]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_11,plain,
% 3.52/0.99      ( v3_setfam_1(X0,X1)
% 3.52/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.52/0.99      | r2_hidden(X1,X0) ),
% 3.52/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1403,plain,
% 3.52/0.99      ( v3_setfam_1(k2_xboole_0(sK3,sK4),X0)
% 3.52/0.99      | ~ m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(X0)))
% 3.52/0.99      | r2_hidden(X0,k2_xboole_0(sK3,sK4)) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1405,plain,
% 3.52/0.99      ( v3_setfam_1(k2_xboole_0(sK3,sK4),sK2)
% 3.52/0.99      | ~ m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK2)))
% 3.52/0.99      | r2_hidden(sK2,k2_xboole_0(sK3,sK4)) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_1403]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_12,plain,
% 3.52/0.99      ( ~ v3_setfam_1(X0,X1)
% 3.52/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.52/0.99      | ~ r2_hidden(X1,X0) ),
% 3.52/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1377,plain,
% 3.52/0.99      ( ~ v3_setfam_1(sK3,sK2) | ~ r2_hidden(sK2,sK3) ),
% 3.52/0.99      inference(resolution,[status(thm)],[c_12,c_18]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1375,plain,
% 3.52/0.99      ( ~ v3_setfam_1(sK4,sK2) | ~ r2_hidden(sK2,sK4) ),
% 3.52/0.99      inference(resolution,[status(thm)],[c_12,c_16]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_10,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.52/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.52/0.99      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 3.52/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_130,plain,
% 3.52/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.52/0.99      inference(prop_impl,[status(thm)],[c_13]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_131,plain,
% 3.52/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.52/0.99      inference(renaming,[status(thm)],[c_130]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_167,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.52/0.99      | ~ r1_tarski(X2,X1)
% 3.52/0.99      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 3.52/0.99      inference(bin_hyper_res,[status(thm)],[c_10,c_131]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_264,plain,
% 3.52/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.52/0.99      inference(prop_impl,[status(thm)],[c_13]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_265,plain,
% 3.52/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.52/0.99      inference(renaming,[status(thm)],[c_264]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_300,plain,
% 3.52/0.99      ( ~ r1_tarski(X0,X1)
% 3.52/0.99      | ~ r1_tarski(X2,X1)
% 3.52/0.99      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 3.52/0.99      inference(bin_hyper_res,[status(thm)],[c_167,c_265]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1280,plain,
% 3.52/0.99      ( ~ r1_tarski(sK4,k1_zfmisc_1(sK2))
% 3.52/0.99      | ~ r1_tarski(sK3,k1_zfmisc_1(sK2))
% 3.52/0.99      | k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_300]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_356,plain,
% 3.52/0.99      ( ~ v3_setfam_1(X0,X1) | v3_setfam_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.52/0.99      theory(equality) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1215,plain,
% 3.52/0.99      ( ~ v3_setfam_1(X0,X1)
% 3.52/0.99      | v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4),sK2)
% 3.52/0.99      | k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4) != X0
% 3.52/0.99      | sK2 != X1 ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_356]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1279,plain,
% 3.52/0.99      ( v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4),sK2)
% 3.52/0.99      | ~ v3_setfam_1(k2_xboole_0(sK3,sK4),X0)
% 3.52/0.99      | k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4) != k2_xboole_0(sK3,sK4)
% 3.52/0.99      | sK2 != X0 ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_1215]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1282,plain,
% 3.52/0.99      ( v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4),sK2)
% 3.52/0.99      | ~ v3_setfam_1(k2_xboole_0(sK3,sK4),sK2)
% 3.52/0.99      | k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4) != k2_xboole_0(sK3,sK4)
% 3.52/0.99      | sK2 != sK2 ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_1279]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_350,plain,( X0 = X0 ),theory(equality) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_363,plain,
% 3.52/0.99      ( sK2 = sK2 ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_350]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_15,negated_conjecture,
% 3.52/0.99      ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK2),sK3,sK4),sK2) ),
% 3.52/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_17,negated_conjecture,
% 3.52/0.99      ( v3_setfam_1(sK4,sK2) ),
% 3.52/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_19,negated_conjecture,
% 3.52/0.99      ( v3_setfam_1(sK3,sK2) ),
% 3.52/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(contradiction,plain,
% 3.52/0.99      ( $false ),
% 3.52/0.99      inference(minisat,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_8302,c_6947,c_1896,c_1405,c_1377,c_1375,c_1280,c_1282,
% 3.52/0.99                 c_974,c_972,c_363,c_15,c_17,c_19]) ).
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  ------                               Statistics
% 3.52/0.99  
% 3.52/0.99  ------ Selected
% 3.52/0.99  
% 3.52/0.99  total_time:                             0.321
% 3.52/0.99  
%------------------------------------------------------------------------------

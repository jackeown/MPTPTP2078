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
% DateTime   : Thu Dec  3 11:41:02 EST 2020

% Result     : Theorem 51.65s
% Output     : CNFRefutation 51.65s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 223 expanded)
%              Number of clauses        :   68 (  76 expanded)
%              Number of leaves         :   11 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  395 (1255 expanded)
%              Number of equality atoms :   72 ( 186 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f29,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> ~ r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f27,plain,(
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

fof(f26,plain,
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

fof(f28,plain,
    ( k3_subset_1(sK2,sK4) != sK3
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK3)
            | r2_hidden(X3,sK4) )
          & ( ~ r2_hidden(X3,sK4)
            | ~ r2_hidden(X3,sK3) ) )
        | ~ m1_subset_1(X3,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f27,f26])).

fof(f46,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK4)
      | ~ r2_hidden(X3,sK3)
      | ~ m1_subset_1(X3,sK2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f30,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK3)
      | r2_hidden(X3,sK4)
      | ~ m1_subset_1(X3,sK2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    k3_subset_1(sK2,sK4) != sK3 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_879,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK3,X1))
    | ~ v1_xboole_0(k4_xboole_0(sK3,X1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7685,plain,
    ( ~ r2_hidden(sK1(X0,X1,sK3),k4_xboole_0(sK3,X2))
    | ~ v1_xboole_0(k4_xboole_0(sK3,X2)) ),
    inference(instantiation,[status(thm)],[c_879])).

cnf(c_95689,plain,
    ( ~ r2_hidden(sK1(X0,sK4,sK3),k4_xboole_0(sK3,X0))
    | ~ v1_xboole_0(k4_xboole_0(sK3,X0)) ),
    inference(instantiation,[status(thm)],[c_7685])).

cnf(c_95691,plain,
    ( ~ r2_hidden(sK1(sK2,sK4,sK3),k4_xboole_0(sK3,sK2))
    | ~ v1_xboole_0(k4_xboole_0(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_95689])).

cnf(c_17,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3978,plain,
    ( ~ m1_subset_1(sK1(X0,X1,sK3),sK2)
    | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
    | ~ r2_hidden(sK1(X0,X1,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_50331,plain,
    ( ~ m1_subset_1(sK1(X0,sK4,sK3),sK2)
    | ~ r2_hidden(sK1(X0,sK4,sK3),sK3)
    | ~ r2_hidden(sK1(X0,sK4,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_3978])).

cnf(c_50347,plain,
    ( ~ m1_subset_1(sK1(sK2,sK4,sK3),sK2)
    | ~ r2_hidden(sK1(sK2,sK4,sK3),sK3)
    | ~ r2_hidden(sK1(sK2,sK4,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_50331])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_16860,plain,
    ( ~ r2_hidden(sK1(X0,sK4,X1),X1)
    | ~ r2_hidden(sK1(X0,sK4,X1),X0)
    | r2_hidden(sK1(X0,sK4,X1),sK4)
    | k4_xboole_0(X0,sK4) = X1 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_38967,plain,
    ( ~ r2_hidden(sK1(X0,sK4,sK3),X0)
    | ~ r2_hidden(sK1(X0,sK4,sK3),sK3)
    | r2_hidden(sK1(X0,sK4,sK3),sK4)
    | k4_xboole_0(X0,sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_16860])).

cnf(c_38973,plain,
    ( ~ r2_hidden(sK1(sK2,sK4,sK3),sK3)
    | r2_hidden(sK1(sK2,sK4,sK3),sK4)
    | ~ r2_hidden(sK1(sK2,sK4,sK3),sK2)
    | k4_xboole_0(sK2,sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_38967])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_688,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,k4_xboole_0(sK3,X1))
    | ~ r2_hidden(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3976,plain,
    ( r2_hidden(sK1(X0,X1,sK3),X2)
    | r2_hidden(sK1(X0,X1,sK3),k4_xboole_0(sK3,X2))
    | ~ r2_hidden(sK1(X0,X1,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_688])).

cnf(c_38966,plain,
    ( r2_hidden(sK1(X0,sK4,sK3),X0)
    | r2_hidden(sK1(X0,sK4,sK3),k4_xboole_0(sK3,X0))
    | ~ r2_hidden(sK1(X0,sK4,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_3976])).

cnf(c_38969,plain,
    ( r2_hidden(sK1(sK2,sK4,sK3),k4_xboole_0(sK3,sK2))
    | ~ r2_hidden(sK1(sK2,sK4,sK3),sK3)
    | r2_hidden(sK1(sK2,sK4,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_38966])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_904,plain,
    ( r2_hidden(sK1(X0,X1,sK3),X0)
    | r2_hidden(sK1(X0,X1,sK3),sK3)
    | k4_xboole_0(X0,X1) = sK3 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_36111,plain,
    ( r2_hidden(sK1(X0,sK4,sK3),X0)
    | r2_hidden(sK1(X0,sK4,sK3),sK3)
    | k4_xboole_0(X0,sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_904])).

cnf(c_36113,plain,
    ( r2_hidden(sK1(sK2,sK4,sK3),sK3)
    | r2_hidden(sK1(sK2,sK4,sK3),sK2)
    | k4_xboole_0(sK2,sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_36111])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_579,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_572,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_792,plain,
    ( r2_hidden(sK0(k4_xboole_0(X0,X1)),X0) = iProver_top
    | v1_xboole_0(k4_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_579,c_572])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_562,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_567,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_568,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1014,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = k4_xboole_0(X0,k3_subset_1(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_567,c_568])).

cnf(c_2588,plain,
    ( k3_subset_1(sK2,k3_subset_1(sK2,sK3)) = k4_xboole_0(sK2,k3_subset_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_562,c_1014])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_566,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_933,plain,
    ( k3_subset_1(sK2,k3_subset_1(sK2,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_562,c_566])).

cnf(c_2935,plain,
    ( k4_xboole_0(sK2,k3_subset_1(sK2,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_2588,c_933])).

cnf(c_21859,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2935,c_572])).

cnf(c_22531,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,X0)),sK2) = iProver_top
    | v1_xboole_0(k4_xboole_0(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_792,c_21859])).

cnf(c_22582,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,X0)),sK2)
    | v1_xboole_0(k4_xboole_0(sK3,X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22531])).

cnf(c_22584,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK2)),sK2)
    | v1_xboole_0(k4_xboole_0(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_22582])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1152,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(X0,X1)),X1)
    | ~ r2_hidden(sK0(k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_19609,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,X0)),X0)
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,X0)),k4_xboole_0(sK3,X0)) ),
    inference(instantiation,[status(thm)],[c_1152])).

cnf(c_19611,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK2)),k4_xboole_0(sK3,sK2))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK2)),sK2) ),
    inference(instantiation,[status(thm)],[c_19609])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_112,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_1])).

cnf(c_113,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_112])).

cnf(c_16967,plain,
    ( m1_subset_1(sK1(X0,sK4,sK3),sK2)
    | ~ r2_hidden(sK1(X0,sK4,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_113])).

cnf(c_16969,plain,
    ( m1_subset_1(sK1(sK2,sK4,sK3),sK2)
    | ~ r2_hidden(sK1(sK2,sK4,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_16967])).

cnf(c_1151,plain,
    ( r2_hidden(sK0(k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))
    | v1_xboole_0(k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3465,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,X0)),k4_xboole_0(sK3,X0))
    | v1_xboole_0(k4_xboole_0(sK3,X0)) ),
    inference(instantiation,[status(thm)],[c_1151])).

cnf(c_3467,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK2)),k4_xboole_0(sK3,sK2))
    | v1_xboole_0(k4_xboole_0(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_3465])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_905,plain,
    ( ~ r2_hidden(sK1(X0,X1,sK3),X1)
    | r2_hidden(sK1(X0,X1,sK3),sK3)
    | k4_xboole_0(X0,X1) = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2638,plain,
    ( r2_hidden(sK1(X0,sK4,sK3),sK3)
    | ~ r2_hidden(sK1(X0,sK4,sK3),sK4)
    | k4_xboole_0(X0,sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_905])).

cnf(c_2644,plain,
    ( r2_hidden(sK1(sK2,sK4,sK3),sK3)
    | ~ r2_hidden(sK1(sK2,sK4,sK3),sK4)
    | k4_xboole_0(sK2,sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_2638])).

cnf(c_16,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | r2_hidden(X0,sK3)
    | r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2637,plain,
    ( ~ m1_subset_1(sK1(X0,sK4,sK3),sK2)
    | r2_hidden(sK1(X0,sK4,sK3),sK3)
    | r2_hidden(sK1(X0,sK4,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2640,plain,
    ( ~ m1_subset_1(sK1(sK2,sK4,sK3),sK2)
    | r2_hidden(sK1(sK2,sK4,sK3),sK3)
    | r2_hidden(sK1(sK2,sK4,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_2637])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_563,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_935,plain,
    ( k3_subset_1(sK2,sK4) = k4_xboole_0(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_563,c_568])).

cnf(c_15,negated_conjecture,
    ( k3_subset_1(sK2,sK4) != sK3 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1684,plain,
    ( k4_xboole_0(sK2,sK4) != sK3 ),
    inference(superposition,[status(thm)],[c_935,c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_95691,c_50347,c_38973,c_38969,c_36113,c_22584,c_19611,c_16969,c_3467,c_2644,c_2640,c_1684])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:08:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 51.65/7.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.65/7.01  
% 51.65/7.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.65/7.01  
% 51.65/7.01  ------  iProver source info
% 51.65/7.01  
% 51.65/7.01  git: date: 2020-06-30 10:37:57 +0100
% 51.65/7.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.65/7.01  git: non_committed_changes: false
% 51.65/7.01  git: last_make_outside_of_git: false
% 51.65/7.01  
% 51.65/7.01  ------ 
% 51.65/7.01  ------ Parsing...
% 51.65/7.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.65/7.01  
% 51.65/7.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 51.65/7.01  
% 51.65/7.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.65/7.01  
% 51.65/7.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.65/7.01  ------ Proving...
% 51.65/7.01  ------ Problem Properties 
% 51.65/7.01  
% 51.65/7.01  
% 51.65/7.01  clauses                                 20
% 51.65/7.01  conjectures                             5
% 51.65/7.01  EPR                                     7
% 51.65/7.01  Horn                                    13
% 51.65/7.01  unary                                   3
% 51.65/7.01  binary                                  8
% 51.65/7.01  lits                                    47
% 51.65/7.01  lits eq                                 6
% 51.65/7.01  fd_pure                                 0
% 51.65/7.01  fd_pseudo                               0
% 51.65/7.01  fd_cond                                 0
% 51.65/7.01  fd_pseudo_cond                          3
% 51.65/7.01  AC symbols                              0
% 51.65/7.01  
% 51.65/7.01  ------ Input Options Time Limit: Unbounded
% 51.65/7.01  
% 51.65/7.01  
% 51.65/7.01  ------ 
% 51.65/7.01  Current options:
% 51.65/7.01  ------ 
% 51.65/7.01  
% 51.65/7.01  
% 51.65/7.01  
% 51.65/7.01  
% 51.65/7.01  ------ Proving...
% 51.65/7.01  
% 51.65/7.01  
% 51.65/7.01  % SZS status Theorem for theBenchmark.p
% 51.65/7.01  
% 51.65/7.01  % SZS output start CNFRefutation for theBenchmark.p
% 51.65/7.01  
% 51.65/7.01  fof(f1,axiom,(
% 51.65/7.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 51.65/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.65/7.01  
% 51.65/7.01  fof(f15,plain,(
% 51.65/7.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 51.65/7.01    inference(nnf_transformation,[],[f1])).
% 51.65/7.01  
% 51.65/7.01  fof(f16,plain,(
% 51.65/7.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 51.65/7.01    inference(rectify,[],[f15])).
% 51.65/7.01  
% 51.65/7.01  fof(f17,plain,(
% 51.65/7.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 51.65/7.01    introduced(choice_axiom,[])).
% 51.65/7.01  
% 51.65/7.01  fof(f18,plain,(
% 51.65/7.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 51.65/7.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 51.65/7.01  
% 51.65/7.01  fof(f29,plain,(
% 51.65/7.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 51.65/7.01    inference(cnf_transformation,[],[f18])).
% 51.65/7.01  
% 51.65/7.01  fof(f7,conjecture,(
% 51.65/7.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 51.65/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.65/7.01  
% 51.65/7.01  fof(f8,negated_conjecture,(
% 51.65/7.01    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 51.65/7.01    inference(negated_conjecture,[],[f7])).
% 51.65/7.01  
% 51.65/7.01  fof(f13,plain,(
% 51.65/7.01    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.65/7.01    inference(ennf_transformation,[],[f8])).
% 51.65/7.01  
% 51.65/7.01  fof(f14,plain,(
% 51.65/7.01    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.65/7.01    inference(flattening,[],[f13])).
% 51.65/7.01  
% 51.65/7.01  fof(f25,plain,(
% 51.65/7.01    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((r2_hidden(X3,X1) | r2_hidden(X3,X2)) & (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.65/7.01    inference(nnf_transformation,[],[f14])).
% 51.65/7.01  
% 51.65/7.01  fof(f27,plain,(
% 51.65/7.01    ( ! [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((r2_hidden(X3,X1) | r2_hidden(X3,X2)) & (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k3_subset_1(X0,sK4) != X1 & ! [X3] : (((r2_hidden(X3,X1) | r2_hidden(X3,sK4)) & (~r2_hidden(X3,sK4) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(sK4,k1_zfmisc_1(X0)))) )),
% 51.65/7.01    introduced(choice_axiom,[])).
% 51.65/7.01  
% 51.65/7.01  fof(f26,plain,(
% 51.65/7.01    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((r2_hidden(X3,X1) | r2_hidden(X3,X2)) & (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k3_subset_1(sK2,X2) != sK3 & ! [X3] : (((r2_hidden(X3,sK3) | r2_hidden(X3,X2)) & (~r2_hidden(X3,X2) | ~r2_hidden(X3,sK3))) | ~m1_subset_1(X3,sK2)) & m1_subset_1(X2,k1_zfmisc_1(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(sK2)))),
% 51.65/7.01    introduced(choice_axiom,[])).
% 51.65/7.01  
% 51.65/7.01  fof(f28,plain,(
% 51.65/7.01    (k3_subset_1(sK2,sK4) != sK3 & ! [X3] : (((r2_hidden(X3,sK3) | r2_hidden(X3,sK4)) & (~r2_hidden(X3,sK4) | ~r2_hidden(X3,sK3))) | ~m1_subset_1(X3,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 51.65/7.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f27,f26])).
% 51.65/7.01  
% 51.65/7.01  fof(f46,plain,(
% 51.65/7.01    ( ! [X3] : (~r2_hidden(X3,sK4) | ~r2_hidden(X3,sK3) | ~m1_subset_1(X3,sK2)) )),
% 51.65/7.01    inference(cnf_transformation,[],[f28])).
% 51.65/7.01  
% 51.65/7.01  fof(f2,axiom,(
% 51.65/7.01    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 51.65/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.65/7.01  
% 51.65/7.01  fof(f19,plain,(
% 51.65/7.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 51.65/7.01    inference(nnf_transformation,[],[f2])).
% 51.65/7.01  
% 51.65/7.01  fof(f20,plain,(
% 51.65/7.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 51.65/7.01    inference(flattening,[],[f19])).
% 51.65/7.01  
% 51.65/7.01  fof(f21,plain,(
% 51.65/7.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 51.65/7.01    inference(rectify,[],[f20])).
% 51.65/7.01  
% 51.65/7.01  fof(f22,plain,(
% 51.65/7.01    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 51.65/7.01    introduced(choice_axiom,[])).
% 51.65/7.01  
% 51.65/7.01  fof(f23,plain,(
% 51.65/7.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 51.65/7.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 51.65/7.01  
% 51.65/7.01  fof(f36,plain,(
% 51.65/7.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 51.65/7.01    inference(cnf_transformation,[],[f23])).
% 51.65/7.01  
% 51.65/7.01  fof(f33,plain,(
% 51.65/7.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 51.65/7.01    inference(cnf_transformation,[],[f23])).
% 51.65/7.01  
% 51.65/7.01  fof(f49,plain,(
% 51.65/7.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 51.65/7.01    inference(equality_resolution,[],[f33])).
% 51.65/7.01  
% 51.65/7.01  fof(f34,plain,(
% 51.65/7.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 51.65/7.01    inference(cnf_transformation,[],[f23])).
% 51.65/7.01  
% 51.65/7.01  fof(f30,plain,(
% 51.65/7.01    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 51.65/7.01    inference(cnf_transformation,[],[f18])).
% 51.65/7.01  
% 51.65/7.01  fof(f31,plain,(
% 51.65/7.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 51.65/7.01    inference(cnf_transformation,[],[f23])).
% 51.65/7.01  
% 51.65/7.01  fof(f51,plain,(
% 51.65/7.01    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 51.65/7.01    inference(equality_resolution,[],[f31])).
% 51.65/7.01  
% 51.65/7.01  fof(f44,plain,(
% 51.65/7.01    m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 51.65/7.01    inference(cnf_transformation,[],[f28])).
% 51.65/7.01  
% 51.65/7.01  fof(f5,axiom,(
% 51.65/7.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 51.65/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.65/7.01  
% 51.65/7.01  fof(f11,plain,(
% 51.65/7.01    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.65/7.01    inference(ennf_transformation,[],[f5])).
% 51.65/7.01  
% 51.65/7.01  fof(f42,plain,(
% 51.65/7.01    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.65/7.01    inference(cnf_transformation,[],[f11])).
% 51.65/7.01  
% 51.65/7.01  fof(f4,axiom,(
% 51.65/7.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 51.65/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.65/7.01  
% 51.65/7.01  fof(f10,plain,(
% 51.65/7.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.65/7.01    inference(ennf_transformation,[],[f4])).
% 51.65/7.01  
% 51.65/7.01  fof(f41,plain,(
% 51.65/7.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.65/7.01    inference(cnf_transformation,[],[f10])).
% 51.65/7.01  
% 51.65/7.01  fof(f6,axiom,(
% 51.65/7.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 51.65/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.65/7.01  
% 51.65/7.01  fof(f12,plain,(
% 51.65/7.01    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.65/7.01    inference(ennf_transformation,[],[f6])).
% 51.65/7.01  
% 51.65/7.01  fof(f43,plain,(
% 51.65/7.01    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.65/7.01    inference(cnf_transformation,[],[f12])).
% 51.65/7.01  
% 51.65/7.01  fof(f32,plain,(
% 51.65/7.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 51.65/7.01    inference(cnf_transformation,[],[f23])).
% 51.65/7.01  
% 51.65/7.01  fof(f50,plain,(
% 51.65/7.01    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 51.65/7.01    inference(equality_resolution,[],[f32])).
% 51.65/7.01  
% 51.65/7.01  fof(f3,axiom,(
% 51.65/7.01    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 51.65/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.65/7.01  
% 51.65/7.01  fof(f9,plain,(
% 51.65/7.01    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 51.65/7.01    inference(ennf_transformation,[],[f3])).
% 51.65/7.01  
% 51.65/7.01  fof(f24,plain,(
% 51.65/7.01    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 51.65/7.01    inference(nnf_transformation,[],[f9])).
% 51.65/7.01  
% 51.65/7.01  fof(f38,plain,(
% 51.65/7.01    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 51.65/7.01    inference(cnf_transformation,[],[f24])).
% 51.65/7.01  
% 51.65/7.01  fof(f35,plain,(
% 51.65/7.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 51.65/7.01    inference(cnf_transformation,[],[f23])).
% 51.65/7.01  
% 51.65/7.01  fof(f47,plain,(
% 51.65/7.01    ( ! [X3] : (r2_hidden(X3,sK3) | r2_hidden(X3,sK4) | ~m1_subset_1(X3,sK2)) )),
% 51.65/7.01    inference(cnf_transformation,[],[f28])).
% 51.65/7.01  
% 51.65/7.01  fof(f45,plain,(
% 51.65/7.01    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 51.65/7.01    inference(cnf_transformation,[],[f28])).
% 51.65/7.01  
% 51.65/7.01  fof(f48,plain,(
% 51.65/7.01    k3_subset_1(sK2,sK4) != sK3),
% 51.65/7.01    inference(cnf_transformation,[],[f28])).
% 51.65/7.01  
% 51.65/7.01  cnf(c_1,plain,
% 51.65/7.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 51.65/7.01      inference(cnf_transformation,[],[f29]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_879,plain,
% 51.65/7.01      ( ~ r2_hidden(X0,k4_xboole_0(sK3,X1))
% 51.65/7.01      | ~ v1_xboole_0(k4_xboole_0(sK3,X1)) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_1]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_7685,plain,
% 51.65/7.01      ( ~ r2_hidden(sK1(X0,X1,sK3),k4_xboole_0(sK3,X2))
% 51.65/7.01      | ~ v1_xboole_0(k4_xboole_0(sK3,X2)) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_879]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_95689,plain,
% 51.65/7.01      ( ~ r2_hidden(sK1(X0,sK4,sK3),k4_xboole_0(sK3,X0))
% 51.65/7.01      | ~ v1_xboole_0(k4_xboole_0(sK3,X0)) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_7685]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_95691,plain,
% 51.65/7.01      ( ~ r2_hidden(sK1(sK2,sK4,sK3),k4_xboole_0(sK3,sK2))
% 51.65/7.01      | ~ v1_xboole_0(k4_xboole_0(sK3,sK2)) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_95689]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_17,negated_conjecture,
% 51.65/7.01      ( ~ m1_subset_1(X0,sK2)
% 51.65/7.01      | ~ r2_hidden(X0,sK3)
% 51.65/7.01      | ~ r2_hidden(X0,sK4) ),
% 51.65/7.01      inference(cnf_transformation,[],[f46]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_3978,plain,
% 51.65/7.01      ( ~ m1_subset_1(sK1(X0,X1,sK3),sK2)
% 51.65/7.01      | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
% 51.65/7.01      | ~ r2_hidden(sK1(X0,X1,sK3),sK4) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_17]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_50331,plain,
% 51.65/7.01      ( ~ m1_subset_1(sK1(X0,sK4,sK3),sK2)
% 51.65/7.01      | ~ r2_hidden(sK1(X0,sK4,sK3),sK3)
% 51.65/7.01      | ~ r2_hidden(sK1(X0,sK4,sK3),sK4) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_3978]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_50347,plain,
% 51.65/7.01      ( ~ m1_subset_1(sK1(sK2,sK4,sK3),sK2)
% 51.65/7.01      | ~ r2_hidden(sK1(sK2,sK4,sK3),sK3)
% 51.65/7.01      | ~ r2_hidden(sK1(sK2,sK4,sK3),sK4) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_50331]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_2,plain,
% 51.65/7.01      ( ~ r2_hidden(sK1(X0,X1,X2),X0)
% 51.65/7.01      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 51.65/7.01      | r2_hidden(sK1(X0,X1,X2),X1)
% 51.65/7.01      | k4_xboole_0(X0,X1) = X2 ),
% 51.65/7.01      inference(cnf_transformation,[],[f36]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_16860,plain,
% 51.65/7.01      ( ~ r2_hidden(sK1(X0,sK4,X1),X1)
% 51.65/7.01      | ~ r2_hidden(sK1(X0,sK4,X1),X0)
% 51.65/7.01      | r2_hidden(sK1(X0,sK4,X1),sK4)
% 51.65/7.01      | k4_xboole_0(X0,sK4) = X1 ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_2]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_38967,plain,
% 51.65/7.01      ( ~ r2_hidden(sK1(X0,sK4,sK3),X0)
% 51.65/7.01      | ~ r2_hidden(sK1(X0,sK4,sK3),sK3)
% 51.65/7.01      | r2_hidden(sK1(X0,sK4,sK3),sK4)
% 51.65/7.01      | k4_xboole_0(X0,sK4) = sK3 ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_16860]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_38973,plain,
% 51.65/7.01      ( ~ r2_hidden(sK1(sK2,sK4,sK3),sK3)
% 51.65/7.01      | r2_hidden(sK1(sK2,sK4,sK3),sK4)
% 51.65/7.01      | ~ r2_hidden(sK1(sK2,sK4,sK3),sK2)
% 51.65/7.01      | k4_xboole_0(sK2,sK4) = sK3 ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_38967]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_5,plain,
% 51.65/7.01      ( ~ r2_hidden(X0,X1)
% 51.65/7.01      | r2_hidden(X0,X2)
% 51.65/7.01      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 51.65/7.01      inference(cnf_transformation,[],[f49]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_688,plain,
% 51.65/7.01      ( r2_hidden(X0,X1)
% 51.65/7.01      | r2_hidden(X0,k4_xboole_0(sK3,X1))
% 51.65/7.01      | ~ r2_hidden(X0,sK3) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_5]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_3976,plain,
% 51.65/7.01      ( r2_hidden(sK1(X0,X1,sK3),X2)
% 51.65/7.01      | r2_hidden(sK1(X0,X1,sK3),k4_xboole_0(sK3,X2))
% 51.65/7.01      | ~ r2_hidden(sK1(X0,X1,sK3),sK3) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_688]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_38966,plain,
% 51.65/7.01      ( r2_hidden(sK1(X0,sK4,sK3),X0)
% 51.65/7.01      | r2_hidden(sK1(X0,sK4,sK3),k4_xboole_0(sK3,X0))
% 51.65/7.01      | ~ r2_hidden(sK1(X0,sK4,sK3),sK3) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_3976]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_38969,plain,
% 51.65/7.01      ( r2_hidden(sK1(sK2,sK4,sK3),k4_xboole_0(sK3,sK2))
% 51.65/7.01      | ~ r2_hidden(sK1(sK2,sK4,sK3),sK3)
% 51.65/7.01      | r2_hidden(sK1(sK2,sK4,sK3),sK2) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_38966]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_4,plain,
% 51.65/7.01      ( r2_hidden(sK1(X0,X1,X2),X0)
% 51.65/7.01      | r2_hidden(sK1(X0,X1,X2),X2)
% 51.65/7.01      | k4_xboole_0(X0,X1) = X2 ),
% 51.65/7.01      inference(cnf_transformation,[],[f34]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_904,plain,
% 51.65/7.01      ( r2_hidden(sK1(X0,X1,sK3),X0)
% 51.65/7.01      | r2_hidden(sK1(X0,X1,sK3),sK3)
% 51.65/7.01      | k4_xboole_0(X0,X1) = sK3 ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_4]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_36111,plain,
% 51.65/7.01      ( r2_hidden(sK1(X0,sK4,sK3),X0)
% 51.65/7.01      | r2_hidden(sK1(X0,sK4,sK3),sK3)
% 51.65/7.01      | k4_xboole_0(X0,sK4) = sK3 ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_904]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_36113,plain,
% 51.65/7.01      ( r2_hidden(sK1(sK2,sK4,sK3),sK3)
% 51.65/7.01      | r2_hidden(sK1(sK2,sK4,sK3),sK2)
% 51.65/7.01      | k4_xboole_0(sK2,sK4) = sK3 ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_36111]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_0,plain,
% 51.65/7.01      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 51.65/7.01      inference(cnf_transformation,[],[f30]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_579,plain,
% 51.65/7.01      ( r2_hidden(sK0(X0),X0) = iProver_top
% 51.65/7.01      | v1_xboole_0(X0) = iProver_top ),
% 51.65/7.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_7,plain,
% 51.65/7.01      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 51.65/7.01      inference(cnf_transformation,[],[f51]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_572,plain,
% 51.65/7.01      ( r2_hidden(X0,X1) = iProver_top
% 51.65/7.01      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 51.65/7.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_792,plain,
% 51.65/7.01      ( r2_hidden(sK0(k4_xboole_0(X0,X1)),X0) = iProver_top
% 51.65/7.01      | v1_xboole_0(k4_xboole_0(X0,X1)) = iProver_top ),
% 51.65/7.01      inference(superposition,[status(thm)],[c_579,c_572]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_19,negated_conjecture,
% 51.65/7.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
% 51.65/7.01      inference(cnf_transformation,[],[f44]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_562,plain,
% 51.65/7.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
% 51.65/7.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_13,plain,
% 51.65/7.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.65/7.01      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 51.65/7.01      inference(cnf_transformation,[],[f42]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_567,plain,
% 51.65/7.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 51.65/7.01      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 51.65/7.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_12,plain,
% 51.65/7.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.65/7.01      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 51.65/7.01      inference(cnf_transformation,[],[f41]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_568,plain,
% 51.65/7.01      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 51.65/7.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 51.65/7.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_1014,plain,
% 51.65/7.01      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = k4_xboole_0(X0,k3_subset_1(X0,X1))
% 51.65/7.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 51.65/7.01      inference(superposition,[status(thm)],[c_567,c_568]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_2588,plain,
% 51.65/7.01      ( k3_subset_1(sK2,k3_subset_1(sK2,sK3)) = k4_xboole_0(sK2,k3_subset_1(sK2,sK3)) ),
% 51.65/7.01      inference(superposition,[status(thm)],[c_562,c_1014]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_14,plain,
% 51.65/7.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.65/7.01      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 51.65/7.01      inference(cnf_transformation,[],[f43]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_566,plain,
% 51.65/7.01      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 51.65/7.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 51.65/7.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_933,plain,
% 51.65/7.01      ( k3_subset_1(sK2,k3_subset_1(sK2,sK3)) = sK3 ),
% 51.65/7.01      inference(superposition,[status(thm)],[c_562,c_566]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_2935,plain,
% 51.65/7.01      ( k4_xboole_0(sK2,k3_subset_1(sK2,sK3)) = sK3 ),
% 51.65/7.01      inference(superposition,[status(thm)],[c_2588,c_933]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_21859,plain,
% 51.65/7.01      ( r2_hidden(X0,sK3) != iProver_top
% 51.65/7.01      | r2_hidden(X0,sK2) = iProver_top ),
% 51.65/7.01      inference(superposition,[status(thm)],[c_2935,c_572]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_22531,plain,
% 51.65/7.01      ( r2_hidden(sK0(k4_xboole_0(sK3,X0)),sK2) = iProver_top
% 51.65/7.01      | v1_xboole_0(k4_xboole_0(sK3,X0)) = iProver_top ),
% 51.65/7.01      inference(superposition,[status(thm)],[c_792,c_21859]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_22582,plain,
% 51.65/7.01      ( r2_hidden(sK0(k4_xboole_0(sK3,X0)),sK2)
% 51.65/7.01      | v1_xboole_0(k4_xboole_0(sK3,X0)) ),
% 51.65/7.01      inference(predicate_to_equality_rev,[status(thm)],[c_22531]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_22584,plain,
% 51.65/7.01      ( r2_hidden(sK0(k4_xboole_0(sK3,sK2)),sK2)
% 51.65/7.01      | v1_xboole_0(k4_xboole_0(sK3,sK2)) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_22582]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_6,plain,
% 51.65/7.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 51.65/7.01      inference(cnf_transformation,[],[f50]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_1152,plain,
% 51.65/7.01      ( ~ r2_hidden(sK0(k4_xboole_0(X0,X1)),X1)
% 51.65/7.01      | ~ r2_hidden(sK0(k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_6]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_19609,plain,
% 51.65/7.01      ( ~ r2_hidden(sK0(k4_xboole_0(sK3,X0)),X0)
% 51.65/7.01      | ~ r2_hidden(sK0(k4_xboole_0(sK3,X0)),k4_xboole_0(sK3,X0)) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_1152]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_19611,plain,
% 51.65/7.01      ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK2)),k4_xboole_0(sK3,sK2))
% 51.65/7.01      | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK2)),sK2) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_19609]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_10,plain,
% 51.65/7.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 51.65/7.01      inference(cnf_transformation,[],[f38]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_112,plain,
% 51.65/7.01      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 51.65/7.01      inference(global_propositional_subsumption,
% 51.65/7.01                [status(thm)],
% 51.65/7.01                [c_10,c_1]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_113,plain,
% 51.65/7.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 51.65/7.01      inference(renaming,[status(thm)],[c_112]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_16967,plain,
% 51.65/7.01      ( m1_subset_1(sK1(X0,sK4,sK3),sK2)
% 51.65/7.01      | ~ r2_hidden(sK1(X0,sK4,sK3),sK2) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_113]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_16969,plain,
% 51.65/7.01      ( m1_subset_1(sK1(sK2,sK4,sK3),sK2)
% 51.65/7.01      | ~ r2_hidden(sK1(sK2,sK4,sK3),sK2) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_16967]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_1151,plain,
% 51.65/7.01      ( r2_hidden(sK0(k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))
% 51.65/7.01      | v1_xboole_0(k4_xboole_0(X0,X1)) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_0]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_3465,plain,
% 51.65/7.01      ( r2_hidden(sK0(k4_xboole_0(sK3,X0)),k4_xboole_0(sK3,X0))
% 51.65/7.01      | v1_xboole_0(k4_xboole_0(sK3,X0)) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_1151]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_3467,plain,
% 51.65/7.01      ( r2_hidden(sK0(k4_xboole_0(sK3,sK2)),k4_xboole_0(sK3,sK2))
% 51.65/7.01      | v1_xboole_0(k4_xboole_0(sK3,sK2)) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_3465]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_3,plain,
% 51.65/7.01      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 51.65/7.01      | r2_hidden(sK1(X0,X1,X2),X2)
% 51.65/7.01      | k4_xboole_0(X0,X1) = X2 ),
% 51.65/7.01      inference(cnf_transformation,[],[f35]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_905,plain,
% 51.65/7.01      ( ~ r2_hidden(sK1(X0,X1,sK3),X1)
% 51.65/7.01      | r2_hidden(sK1(X0,X1,sK3),sK3)
% 51.65/7.01      | k4_xboole_0(X0,X1) = sK3 ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_3]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_2638,plain,
% 51.65/7.01      ( r2_hidden(sK1(X0,sK4,sK3),sK3)
% 51.65/7.01      | ~ r2_hidden(sK1(X0,sK4,sK3),sK4)
% 51.65/7.01      | k4_xboole_0(X0,sK4) = sK3 ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_905]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_2644,plain,
% 51.65/7.01      ( r2_hidden(sK1(sK2,sK4,sK3),sK3)
% 51.65/7.01      | ~ r2_hidden(sK1(sK2,sK4,sK3),sK4)
% 51.65/7.01      | k4_xboole_0(sK2,sK4) = sK3 ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_2638]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_16,negated_conjecture,
% 51.65/7.01      ( ~ m1_subset_1(X0,sK2) | r2_hidden(X0,sK3) | r2_hidden(X0,sK4) ),
% 51.65/7.01      inference(cnf_transformation,[],[f47]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_2637,plain,
% 51.65/7.01      ( ~ m1_subset_1(sK1(X0,sK4,sK3),sK2)
% 51.65/7.01      | r2_hidden(sK1(X0,sK4,sK3),sK3)
% 51.65/7.01      | r2_hidden(sK1(X0,sK4,sK3),sK4) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_16]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_2640,plain,
% 51.65/7.01      ( ~ m1_subset_1(sK1(sK2,sK4,sK3),sK2)
% 51.65/7.01      | r2_hidden(sK1(sK2,sK4,sK3),sK3)
% 51.65/7.01      | r2_hidden(sK1(sK2,sK4,sK3),sK4) ),
% 51.65/7.01      inference(instantiation,[status(thm)],[c_2637]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_18,negated_conjecture,
% 51.65/7.01      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 51.65/7.01      inference(cnf_transformation,[],[f45]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_563,plain,
% 51.65/7.01      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 51.65/7.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_935,plain,
% 51.65/7.01      ( k3_subset_1(sK2,sK4) = k4_xboole_0(sK2,sK4) ),
% 51.65/7.01      inference(superposition,[status(thm)],[c_563,c_568]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_15,negated_conjecture,
% 51.65/7.01      ( k3_subset_1(sK2,sK4) != sK3 ),
% 51.65/7.01      inference(cnf_transformation,[],[f48]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(c_1684,plain,
% 51.65/7.01      ( k4_xboole_0(sK2,sK4) != sK3 ),
% 51.65/7.01      inference(superposition,[status(thm)],[c_935,c_15]) ).
% 51.65/7.01  
% 51.65/7.01  cnf(contradiction,plain,
% 51.65/7.01      ( $false ),
% 51.65/7.01      inference(minisat,
% 51.65/7.01                [status(thm)],
% 51.65/7.01                [c_95691,c_50347,c_38973,c_38969,c_36113,c_22584,c_19611,
% 51.65/7.01                 c_16969,c_3467,c_2644,c_2640,c_1684]) ).
% 51.65/7.01  
% 51.65/7.01  
% 51.65/7.01  % SZS output end CNFRefutation for theBenchmark.p
% 51.65/7.01  
% 51.65/7.01  ------                               Statistics
% 51.65/7.01  
% 51.65/7.01  ------ Selected
% 51.65/7.01  
% 51.65/7.01  total_time:                             6.194
% 51.65/7.01  
%------------------------------------------------------------------------------

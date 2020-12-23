%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:03 EST 2020

% Result     : Theorem 11.51s
% Output     : CNFRefutation 11.51s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 177 expanded)
%              Number of clauses        :   58 (  60 expanded)
%              Number of leaves         :   11 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  435 (1343 expanded)
%              Number of equality atoms :   78 ( 174 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ( r2_hidden(X4,X1)
                    <=> ( ~ r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) ) ) )
               => k7_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,X1)
                      <=> ( ~ r2_hidden(X4,X3)
                          & r2_hidden(X4,X2) ) ) )
                 => k7_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( ~ r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( ~ r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( ~ r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( ~ r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k7_subset_1(X0,X2,X3) != X1
          & ! [X4] :
              ( ( ( r2_hidden(X4,X1)
                  | r2_hidden(X4,X3)
                  | ~ r2_hidden(X4,X2) )
                & ( ( ~ r2_hidden(X4,X3)
                    & r2_hidden(X4,X2) )
                  | ~ r2_hidden(X4,X1) ) )
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( k7_subset_1(X0,X2,sK5) != X1
        & ! [X4] :
            ( ( ( r2_hidden(X4,X1)
                | r2_hidden(X4,sK5)
                | ~ r2_hidden(X4,X2) )
              & ( ( ~ r2_hidden(X4,sK5)
                  & r2_hidden(X4,X2) )
                | ~ r2_hidden(X4,X1) ) )
            | ~ m1_subset_1(X4,X0) )
        & m1_subset_1(sK5,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( ~ r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ? [X3] :
            ( k7_subset_1(X0,sK4,X3) != X1
            & ! [X4] :
                ( ( ( r2_hidden(X4,X1)
                    | r2_hidden(X4,X3)
                    | ~ r2_hidden(X4,sK4) )
                  & ( ( ~ r2_hidden(X4,X3)
                      & r2_hidden(X4,sK4) )
                    | ~ r2_hidden(X4,X1) ) )
                | ~ m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(X0)) )
        & m1_subset_1(sK4,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k7_subset_1(X0,X2,X3) != X1
                & ! [X4] :
                    ( ( ( r2_hidden(X4,X1)
                        | r2_hidden(X4,X3)
                        | ~ r2_hidden(X4,X2) )
                      & ( ( ~ r2_hidden(X4,X3)
                          & r2_hidden(X4,X2) )
                        | ~ r2_hidden(X4,X1) ) )
                    | ~ m1_subset_1(X4,X0) )
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k7_subset_1(sK2,X2,X3) != sK3
              & ! [X4] :
                  ( ( ( r2_hidden(X4,sK3)
                      | r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( ~ r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,sK3) ) )
                  | ~ m1_subset_1(X4,sK2) )
              & m1_subset_1(X3,k1_zfmisc_1(sK2)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( k7_subset_1(sK2,sK4,sK5) != sK3
    & ! [X4] :
        ( ( ( r2_hidden(X4,sK3)
            | r2_hidden(X4,sK5)
            | ~ r2_hidden(X4,sK4) )
          & ( ( ~ r2_hidden(X4,sK5)
              & r2_hidden(X4,sK4) )
            | ~ r2_hidden(X4,sK3) ) )
        | ~ m1_subset_1(X4,sK2) )
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f27,f26,f25])).

fof(f47,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK5)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f29,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

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
    inference(flattening,[],[f17])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X4] :
      ( r2_hidden(X4,sK4)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    ! [X4] :
      ( r2_hidden(X4,sK3)
      | r2_hidden(X4,sK5)
      | ~ r2_hidden(X4,sK4)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    k7_subset_1(sK2,sK4,sK5) != sK3 ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1634,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X0,X2,X3),X0)
    | r2_hidden(sK1(X0,X2,X3),X1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2424,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X0,X2,sK3),X0)
    | r2_hidden(sK1(X0,X2,sK3),X1) ),
    inference(instantiation,[status(thm)],[c_1634])).

cnf(c_4936,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK1(sK4,X0,sK3),sK4)
    | r2_hidden(sK1(sK4,X0,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_2424])).

cnf(c_30225,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK4)
    | r2_hidden(sK1(sK4,sK5,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_4936])).

cnf(c_30228,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK4) != iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30225])).

cnf(c_16,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1597,plain,
    ( ~ m1_subset_1(sK1(X0,X1,sK3),sK2)
    | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
    | ~ r2_hidden(sK1(X0,X1,sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2894,plain,
    ( ~ m1_subset_1(sK1(X0,sK5,sK3),sK2)
    | ~ r2_hidden(sK1(X0,sK5,sK3),sK3)
    | ~ r2_hidden(sK1(X0,sK5,sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_1597])).

cnf(c_21185,plain,
    ( ~ m1_subset_1(sK1(sK4,sK5,sK3),sK2)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_2894])).

cnf(c_21188,plain,
    ( m1_subset_1(sK1(sK4,sK5,sK3),sK2) != iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21185])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_115,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_1])).

cnf(c_116,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_115])).

cnf(c_1695,plain,
    ( m1_subset_1(sK1(X0,X1,sK3),sK2)
    | ~ r2_hidden(sK1(X0,X1,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_2858,plain,
    ( m1_subset_1(sK1(sK4,X0,sK3),sK2)
    | ~ r2_hidden(sK1(sK4,X0,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_1695])).

cnf(c_21183,plain,
    ( m1_subset_1(sK1(sK4,sK5,sK3),sK2)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_2858])).

cnf(c_21186,plain,
    ( m1_subset_1(sK1(sK4,sK5,sK3),sK2) = iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21183])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1348,plain,
    ( ~ r2_hidden(sK1(X0,X1,sK3),X1)
    | r2_hidden(sK1(X0,X1,sK3),sK3)
    | k4_xboole_0(X0,X1) = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5385,plain,
    ( r2_hidden(sK1(X0,sK5,sK3),sK3)
    | ~ r2_hidden(sK1(X0,sK5,sK3),sK5)
    | k4_xboole_0(X0,sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_1348])).

cnf(c_15962,plain,
    ( r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK5)
    | k4_xboole_0(sK4,sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_5385])).

cnf(c_15963,plain,
    ( k4_xboole_0(sK4,sK5) = sK3
    | r2_hidden(sK1(sK4,sK5,sK3),sK3) = iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15962])).

cnf(c_1591,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r2_hidden(sK1(X1,X2,sK3),X0)
    | ~ r2_hidden(sK1(X1,X2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_4913,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK1(sK4,X0,sK3),sK3)
    | r2_hidden(sK1(sK4,X0,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_1591])).

cnf(c_12696,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | r2_hidden(sK1(sK4,sK5,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_4913])).

cnf(c_12697,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12696])).

cnf(c_17,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,sK3)
    | r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1596,plain,
    ( ~ m1_subset_1(sK1(X0,X1,sK3),sK2)
    | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
    | r2_hidden(sK1(X0,X1,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_12271,plain,
    ( ~ m1_subset_1(sK1(sK4,sK5,sK3),sK2)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | r2_hidden(sK1(sK4,sK5,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1596])).

cnf(c_12275,plain,
    ( m1_subset_1(sK1(sK4,sK5,sK3),sK2) != iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12271])).

cnf(c_15,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | r2_hidden(X0,sK3)
    | r2_hidden(X0,sK5)
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1638,plain,
    ( ~ m1_subset_1(sK1(sK4,X0,X1),sK2)
    | r2_hidden(sK1(sK4,X0,X1),sK3)
    | r2_hidden(sK1(sK4,X0,X1),sK5)
    | ~ r2_hidden(sK1(sK4,X0,X1),sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2859,plain,
    ( ~ m1_subset_1(sK1(sK4,X0,sK3),sK2)
    | r2_hidden(sK1(sK4,X0,sK3),sK3)
    | r2_hidden(sK1(sK4,X0,sK3),sK5)
    | ~ r2_hidden(sK1(sK4,X0,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1638])).

cnf(c_5419,plain,
    ( ~ m1_subset_1(sK1(sK4,sK5,sK3),sK2)
    | r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | r2_hidden(sK1(sK4,sK5,sK3),sK5)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_2859])).

cnf(c_5425,plain,
    ( m1_subset_1(sK1(sK4,sK5,sK3),sK2) != iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK3) = iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK5) = iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5419])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1637,plain,
    ( r2_hidden(sK1(sK4,X0,X1),X1)
    | r2_hidden(sK1(sK4,X0,X1),sK4)
    | k4_xboole_0(sK4,X0) = X1 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1737,plain,
    ( r2_hidden(sK1(sK4,X0,sK3),sK3)
    | r2_hidden(sK1(sK4,X0,sK3),sK4)
    | k4_xboole_0(sK4,X0) = sK3 ),
    inference(instantiation,[status(thm)],[c_1637])).

cnf(c_5420,plain,
    ( r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | r2_hidden(sK1(sK4,sK5,sK3),sK4)
    | k4_xboole_0(sK4,sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_1737])).

cnf(c_5423,plain,
    ( k4_xboole_0(sK4,sK5) = sK3
    | r2_hidden(sK1(sK4,sK5,sK3),sK3) = iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5420])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1346,plain,
    ( ~ r2_hidden(sK1(X0,X1,sK3),X0)
    | r2_hidden(sK1(X0,X1,sK3),X1)
    | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
    | k4_xboole_0(X0,X1) = sK3 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2895,plain,
    ( ~ r2_hidden(sK1(X0,sK5,sK3),X0)
    | ~ r2_hidden(sK1(X0,sK5,sK3),sK3)
    | r2_hidden(sK1(X0,sK5,sK3),sK5)
    | k4_xboole_0(X0,sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_1346])).

cnf(c_5418,plain,
    ( ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | r2_hidden(sK1(sK4,sK5,sK3),sK5)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK4)
    | k4_xboole_0(sK4,sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_2895])).

cnf(c_5421,plain,
    ( k4_xboole_0(sK4,sK5) = sK3
    | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK5) = iProver_top
    | r2_hidden(sK1(sK4,sK5,sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5418])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1059,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1064,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1375,plain,
    ( k7_subset_1(sK2,sK4,X0) = k4_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1059,c_1064])).

cnf(c_14,negated_conjecture,
    ( k7_subset_1(sK2,sK4,sK5) != sK3 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1553,plain,
    ( k4_xboole_0(sK4,sK5) != sK3 ),
    inference(demodulation,[status(thm)],[c_1375,c_14])).

cnf(c_22,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30228,c_21188,c_21186,c_15963,c_12697,c_12275,c_5425,c_5423,c_5421,c_1553,c_22,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 11.51/1.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.51/1.94  
% 11.51/1.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.51/1.94  
% 11.51/1.94  ------  iProver source info
% 11.51/1.94  
% 11.51/1.94  git: date: 2020-06-30 10:37:57 +0100
% 11.51/1.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.51/1.94  git: non_committed_changes: false
% 11.51/1.94  git: last_make_outside_of_git: false
% 11.51/1.94  
% 11.51/1.94  ------ 
% 11.51/1.94  
% 11.51/1.94  ------ Input Options
% 11.51/1.94  
% 11.51/1.94  --out_options                           all
% 11.51/1.94  --tptp_safe_out                         true
% 11.51/1.94  --problem_path                          ""
% 11.51/1.94  --include_path                          ""
% 11.51/1.94  --clausifier                            res/vclausify_rel
% 11.51/1.94  --clausifier_options                    --mode clausify
% 11.51/1.94  --stdin                                 false
% 11.51/1.94  --stats_out                             all
% 11.51/1.94  
% 11.51/1.94  ------ General Options
% 11.51/1.94  
% 11.51/1.94  --fof                                   false
% 11.51/1.94  --time_out_real                         305.
% 11.51/1.94  --time_out_virtual                      -1.
% 11.51/1.94  --symbol_type_check                     false
% 11.51/1.94  --clausify_out                          false
% 11.51/1.94  --sig_cnt_out                           false
% 11.51/1.94  --trig_cnt_out                          false
% 11.51/1.94  --trig_cnt_out_tolerance                1.
% 11.51/1.94  --trig_cnt_out_sk_spl                   false
% 11.51/1.94  --abstr_cl_out                          false
% 11.51/1.94  
% 11.51/1.94  ------ Global Options
% 11.51/1.94  
% 11.51/1.94  --schedule                              default
% 11.51/1.94  --add_important_lit                     false
% 11.51/1.94  --prop_solver_per_cl                    1000
% 11.51/1.94  --min_unsat_core                        false
% 11.51/1.94  --soft_assumptions                      false
% 11.51/1.94  --soft_lemma_size                       3
% 11.51/1.94  --prop_impl_unit_size                   0
% 11.51/1.94  --prop_impl_unit                        []
% 11.51/1.94  --share_sel_clauses                     true
% 11.51/1.94  --reset_solvers                         false
% 11.51/1.94  --bc_imp_inh                            [conj_cone]
% 11.51/1.94  --conj_cone_tolerance                   3.
% 11.51/1.94  --extra_neg_conj                        none
% 11.51/1.94  --large_theory_mode                     true
% 11.51/1.94  --prolific_symb_bound                   200
% 11.51/1.94  --lt_threshold                          2000
% 11.51/1.94  --clause_weak_htbl                      true
% 11.51/1.94  --gc_record_bc_elim                     false
% 11.51/1.94  
% 11.51/1.94  ------ Preprocessing Options
% 11.51/1.94  
% 11.51/1.94  --preprocessing_flag                    true
% 11.51/1.94  --time_out_prep_mult                    0.1
% 11.51/1.94  --splitting_mode                        input
% 11.51/1.94  --splitting_grd                         true
% 11.51/1.94  --splitting_cvd                         false
% 11.51/1.94  --splitting_cvd_svl                     false
% 11.51/1.94  --splitting_nvd                         32
% 11.51/1.94  --sub_typing                            true
% 11.51/1.94  --prep_gs_sim                           true
% 11.51/1.94  --prep_unflatten                        true
% 11.51/1.94  --prep_res_sim                          true
% 11.51/1.94  --prep_upred                            true
% 11.51/1.94  --prep_sem_filter                       exhaustive
% 11.51/1.94  --prep_sem_filter_out                   false
% 11.51/1.94  --pred_elim                             true
% 11.51/1.94  --res_sim_input                         true
% 11.51/1.94  --eq_ax_congr_red                       true
% 11.51/1.94  --pure_diseq_elim                       true
% 11.51/1.94  --brand_transform                       false
% 11.51/1.94  --non_eq_to_eq                          false
% 11.51/1.94  --prep_def_merge                        true
% 11.51/1.94  --prep_def_merge_prop_impl              false
% 11.51/1.94  --prep_def_merge_mbd                    true
% 11.51/1.94  --prep_def_merge_tr_red                 false
% 11.51/1.94  --prep_def_merge_tr_cl                  false
% 11.51/1.94  --smt_preprocessing                     true
% 11.51/1.94  --smt_ac_axioms                         fast
% 11.51/1.94  --preprocessed_out                      false
% 11.51/1.94  --preprocessed_stats                    false
% 11.51/1.94  
% 11.51/1.94  ------ Abstraction refinement Options
% 11.51/1.94  
% 11.51/1.94  --abstr_ref                             []
% 11.51/1.94  --abstr_ref_prep                        false
% 11.51/1.94  --abstr_ref_until_sat                   false
% 11.51/1.94  --abstr_ref_sig_restrict                funpre
% 11.51/1.94  --abstr_ref_af_restrict_to_split_sk     false
% 11.51/1.94  --abstr_ref_under                       []
% 11.51/1.94  
% 11.51/1.94  ------ SAT Options
% 11.51/1.94  
% 11.51/1.94  --sat_mode                              false
% 11.51/1.94  --sat_fm_restart_options                ""
% 11.51/1.94  --sat_gr_def                            false
% 11.51/1.94  --sat_epr_types                         true
% 11.51/1.94  --sat_non_cyclic_types                  false
% 11.51/1.94  --sat_finite_models                     false
% 11.51/1.94  --sat_fm_lemmas                         false
% 11.51/1.94  --sat_fm_prep                           false
% 11.51/1.94  --sat_fm_uc_incr                        true
% 11.51/1.94  --sat_out_model                         small
% 11.51/1.94  --sat_out_clauses                       false
% 11.51/1.94  
% 11.51/1.94  ------ QBF Options
% 11.51/1.94  
% 11.51/1.94  --qbf_mode                              false
% 11.51/1.94  --qbf_elim_univ                         false
% 11.51/1.94  --qbf_dom_inst                          none
% 11.51/1.94  --qbf_dom_pre_inst                      false
% 11.51/1.94  --qbf_sk_in                             false
% 11.51/1.94  --qbf_pred_elim                         true
% 11.51/1.94  --qbf_split                             512
% 11.51/1.94  
% 11.51/1.94  ------ BMC1 Options
% 11.51/1.94  
% 11.51/1.94  --bmc1_incremental                      false
% 11.51/1.94  --bmc1_axioms                           reachable_all
% 11.51/1.94  --bmc1_min_bound                        0
% 11.51/1.94  --bmc1_max_bound                        -1
% 11.51/1.94  --bmc1_max_bound_default                -1
% 11.51/1.94  --bmc1_symbol_reachability              true
% 11.51/1.94  --bmc1_property_lemmas                  false
% 11.51/1.94  --bmc1_k_induction                      false
% 11.51/1.94  --bmc1_non_equiv_states                 false
% 11.51/1.94  --bmc1_deadlock                         false
% 11.51/1.94  --bmc1_ucm                              false
% 11.51/1.94  --bmc1_add_unsat_core                   none
% 11.51/1.94  --bmc1_unsat_core_children              false
% 11.51/1.94  --bmc1_unsat_core_extrapolate_axioms    false
% 11.51/1.94  --bmc1_out_stat                         full
% 11.51/1.94  --bmc1_ground_init                      false
% 11.51/1.94  --bmc1_pre_inst_next_state              false
% 11.51/1.94  --bmc1_pre_inst_state                   false
% 11.51/1.94  --bmc1_pre_inst_reach_state             false
% 11.51/1.94  --bmc1_out_unsat_core                   false
% 11.51/1.94  --bmc1_aig_witness_out                  false
% 11.51/1.94  --bmc1_verbose                          false
% 11.51/1.94  --bmc1_dump_clauses_tptp                false
% 11.51/1.94  --bmc1_dump_unsat_core_tptp             false
% 11.51/1.94  --bmc1_dump_file                        -
% 11.51/1.94  --bmc1_ucm_expand_uc_limit              128
% 11.51/1.94  --bmc1_ucm_n_expand_iterations          6
% 11.51/1.94  --bmc1_ucm_extend_mode                  1
% 11.51/1.94  --bmc1_ucm_init_mode                    2
% 11.51/1.94  --bmc1_ucm_cone_mode                    none
% 11.51/1.94  --bmc1_ucm_reduced_relation_type        0
% 11.51/1.94  --bmc1_ucm_relax_model                  4
% 11.51/1.94  --bmc1_ucm_full_tr_after_sat            true
% 11.51/1.94  --bmc1_ucm_expand_neg_assumptions       false
% 11.51/1.94  --bmc1_ucm_layered_model                none
% 11.51/1.94  --bmc1_ucm_max_lemma_size               10
% 11.51/1.94  
% 11.51/1.94  ------ AIG Options
% 11.51/1.94  
% 11.51/1.94  --aig_mode                              false
% 11.51/1.94  
% 11.51/1.94  ------ Instantiation Options
% 11.51/1.94  
% 11.51/1.94  --instantiation_flag                    true
% 11.51/1.94  --inst_sos_flag                         false
% 11.51/1.94  --inst_sos_phase                        true
% 11.51/1.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.51/1.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.51/1.94  --inst_lit_sel_side                     num_symb
% 11.51/1.94  --inst_solver_per_active                1400
% 11.51/1.94  --inst_solver_calls_frac                1.
% 11.51/1.94  --inst_passive_queue_type               priority_queues
% 11.51/1.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.51/1.94  --inst_passive_queues_freq              [25;2]
% 11.51/1.94  --inst_dismatching                      true
% 11.51/1.94  --inst_eager_unprocessed_to_passive     true
% 11.51/1.94  --inst_prop_sim_given                   true
% 11.51/1.94  --inst_prop_sim_new                     false
% 11.51/1.94  --inst_subs_new                         false
% 11.51/1.94  --inst_eq_res_simp                      false
% 11.51/1.94  --inst_subs_given                       false
% 11.51/1.94  --inst_orphan_elimination               true
% 11.51/1.94  --inst_learning_loop_flag               true
% 11.51/1.94  --inst_learning_start                   3000
% 11.51/1.94  --inst_learning_factor                  2
% 11.51/1.94  --inst_start_prop_sim_after_learn       3
% 11.51/1.94  --inst_sel_renew                        solver
% 11.51/1.94  --inst_lit_activity_flag                true
% 11.51/1.94  --inst_restr_to_given                   false
% 11.51/1.94  --inst_activity_threshold               500
% 11.51/1.94  --inst_out_proof                        true
% 11.51/1.94  
% 11.51/1.94  ------ Resolution Options
% 11.51/1.94  
% 11.51/1.94  --resolution_flag                       true
% 11.51/1.94  --res_lit_sel                           adaptive
% 11.51/1.94  --res_lit_sel_side                      none
% 11.51/1.94  --res_ordering                          kbo
% 11.51/1.94  --res_to_prop_solver                    active
% 11.51/1.94  --res_prop_simpl_new                    false
% 11.51/1.94  --res_prop_simpl_given                  true
% 11.51/1.94  --res_passive_queue_type                priority_queues
% 11.51/1.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.51/1.94  --res_passive_queues_freq               [15;5]
% 11.51/1.94  --res_forward_subs                      full
% 11.51/1.94  --res_backward_subs                     full
% 11.51/1.94  --res_forward_subs_resolution           true
% 11.51/1.94  --res_backward_subs_resolution          true
% 11.51/1.94  --res_orphan_elimination                true
% 11.51/1.94  --res_time_limit                        2.
% 11.51/1.94  --res_out_proof                         true
% 11.51/1.94  
% 11.51/1.94  ------ Superposition Options
% 11.51/1.94  
% 11.51/1.94  --superposition_flag                    true
% 11.51/1.94  --sup_passive_queue_type                priority_queues
% 11.51/1.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.51/1.94  --sup_passive_queues_freq               [8;1;4]
% 11.51/1.94  --demod_completeness_check              fast
% 11.51/1.94  --demod_use_ground                      true
% 11.51/1.94  --sup_to_prop_solver                    passive
% 11.51/1.94  --sup_prop_simpl_new                    true
% 11.51/1.94  --sup_prop_simpl_given                  true
% 11.51/1.94  --sup_fun_splitting                     false
% 11.51/1.94  --sup_smt_interval                      50000
% 11.51/1.94  
% 11.51/1.94  ------ Superposition Simplification Setup
% 11.51/1.94  
% 11.51/1.94  --sup_indices_passive                   []
% 11.51/1.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.51/1.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.51/1.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.51/1.94  --sup_full_triv                         [TrivRules;PropSubs]
% 11.51/1.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.51/1.94  --sup_full_bw                           [BwDemod]
% 11.51/1.94  --sup_immed_triv                        [TrivRules]
% 11.51/1.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.51/1.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.51/1.94  --sup_immed_bw_main                     []
% 11.51/1.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.51/1.94  --sup_input_triv                        [Unflattening;TrivRules]
% 11.51/1.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.51/1.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.51/1.94  
% 11.51/1.94  ------ Combination Options
% 11.51/1.94  
% 11.51/1.94  --comb_res_mult                         3
% 11.51/1.94  --comb_sup_mult                         2
% 11.51/1.94  --comb_inst_mult                        10
% 11.51/1.94  
% 11.51/1.94  ------ Debug Options
% 11.51/1.94  
% 11.51/1.94  --dbg_backtrace                         false
% 11.51/1.94  --dbg_dump_prop_clauses                 false
% 11.51/1.94  --dbg_dump_prop_clauses_file            -
% 11.51/1.94  --dbg_out_stat                          false
% 11.51/1.94  ------ Parsing...
% 11.51/1.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.51/1.94  
% 11.51/1.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.51/1.94  
% 11.51/1.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.51/1.94  
% 11.51/1.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.51/1.94  ------ Proving...
% 11.51/1.94  ------ Problem Properties 
% 11.51/1.94  
% 11.51/1.94  
% 11.51/1.94  clauses                                 21
% 11.51/1.94  conjectures                             7
% 11.51/1.94  EPR                                     8
% 11.51/1.94  Horn                                    14
% 11.51/1.94  unary                                   4
% 11.51/1.94  binary                                  6
% 11.51/1.94  lits                                    51
% 11.51/1.94  lits eq                                 5
% 11.51/1.94  fd_pure                                 0
% 11.51/1.94  fd_pseudo                               0
% 11.51/1.94  fd_cond                                 0
% 11.51/1.94  fd_pseudo_cond                          3
% 11.51/1.94  AC symbols                              0
% 11.51/1.94  
% 11.51/1.94  ------ Schedule dynamic 5 is on 
% 11.51/1.94  
% 11.51/1.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.51/1.94  
% 11.51/1.94  
% 11.51/1.94  ------ 
% 11.51/1.94  Current options:
% 11.51/1.94  ------ 
% 11.51/1.94  
% 11.51/1.94  ------ Input Options
% 11.51/1.94  
% 11.51/1.94  --out_options                           all
% 11.51/1.94  --tptp_safe_out                         true
% 11.51/1.94  --problem_path                          ""
% 11.51/1.94  --include_path                          ""
% 11.51/1.94  --clausifier                            res/vclausify_rel
% 11.51/1.94  --clausifier_options                    --mode clausify
% 11.51/1.94  --stdin                                 false
% 11.51/1.94  --stats_out                             all
% 11.51/1.94  
% 11.51/1.94  ------ General Options
% 11.51/1.94  
% 11.51/1.94  --fof                                   false
% 11.51/1.94  --time_out_real                         305.
% 11.51/1.94  --time_out_virtual                      -1.
% 11.51/1.94  --symbol_type_check                     false
% 11.51/1.94  --clausify_out                          false
% 11.51/1.94  --sig_cnt_out                           false
% 11.51/1.94  --trig_cnt_out                          false
% 11.51/1.94  --trig_cnt_out_tolerance                1.
% 11.51/1.94  --trig_cnt_out_sk_spl                   false
% 11.51/1.94  --abstr_cl_out                          false
% 11.51/1.94  
% 11.51/1.94  ------ Global Options
% 11.51/1.94  
% 11.51/1.94  --schedule                              default
% 11.51/1.94  --add_important_lit                     false
% 11.51/1.94  --prop_solver_per_cl                    1000
% 11.51/1.94  --min_unsat_core                        false
% 11.51/1.94  --soft_assumptions                      false
% 11.51/1.94  --soft_lemma_size                       3
% 11.51/1.94  --prop_impl_unit_size                   0
% 11.51/1.94  --prop_impl_unit                        []
% 11.51/1.94  --share_sel_clauses                     true
% 11.51/1.94  --reset_solvers                         false
% 11.51/1.94  --bc_imp_inh                            [conj_cone]
% 11.51/1.94  --conj_cone_tolerance                   3.
% 11.51/1.94  --extra_neg_conj                        none
% 11.51/1.94  --large_theory_mode                     true
% 11.51/1.94  --prolific_symb_bound                   200
% 11.51/1.94  --lt_threshold                          2000
% 11.51/1.94  --clause_weak_htbl                      true
% 11.51/1.94  --gc_record_bc_elim                     false
% 11.51/1.94  
% 11.51/1.94  ------ Preprocessing Options
% 11.51/1.94  
% 11.51/1.94  --preprocessing_flag                    true
% 11.51/1.94  --time_out_prep_mult                    0.1
% 11.51/1.94  --splitting_mode                        input
% 11.51/1.94  --splitting_grd                         true
% 11.51/1.94  --splitting_cvd                         false
% 11.51/1.94  --splitting_cvd_svl                     false
% 11.51/1.94  --splitting_nvd                         32
% 11.51/1.94  --sub_typing                            true
% 11.51/1.94  --prep_gs_sim                           true
% 11.51/1.94  --prep_unflatten                        true
% 11.51/1.94  --prep_res_sim                          true
% 11.51/1.94  --prep_upred                            true
% 11.51/1.94  --prep_sem_filter                       exhaustive
% 11.51/1.94  --prep_sem_filter_out                   false
% 11.51/1.94  --pred_elim                             true
% 11.51/1.94  --res_sim_input                         true
% 11.51/1.94  --eq_ax_congr_red                       true
% 11.51/1.94  --pure_diseq_elim                       true
% 11.51/1.94  --brand_transform                       false
% 11.51/1.94  --non_eq_to_eq                          false
% 11.51/1.94  --prep_def_merge                        true
% 11.51/1.94  --prep_def_merge_prop_impl              false
% 11.51/1.94  --prep_def_merge_mbd                    true
% 11.51/1.94  --prep_def_merge_tr_red                 false
% 11.51/1.94  --prep_def_merge_tr_cl                  false
% 11.51/1.94  --smt_preprocessing                     true
% 11.51/1.94  --smt_ac_axioms                         fast
% 11.51/1.94  --preprocessed_out                      false
% 11.51/1.94  --preprocessed_stats                    false
% 11.51/1.94  
% 11.51/1.94  ------ Abstraction refinement Options
% 11.51/1.94  
% 11.51/1.94  --abstr_ref                             []
% 11.51/1.94  --abstr_ref_prep                        false
% 11.51/1.94  --abstr_ref_until_sat                   false
% 11.51/1.94  --abstr_ref_sig_restrict                funpre
% 11.51/1.94  --abstr_ref_af_restrict_to_split_sk     false
% 11.51/1.94  --abstr_ref_under                       []
% 11.51/1.94  
% 11.51/1.94  ------ SAT Options
% 11.51/1.94  
% 11.51/1.94  --sat_mode                              false
% 11.51/1.94  --sat_fm_restart_options                ""
% 11.51/1.94  --sat_gr_def                            false
% 11.51/1.94  --sat_epr_types                         true
% 11.51/1.94  --sat_non_cyclic_types                  false
% 11.51/1.94  --sat_finite_models                     false
% 11.51/1.94  --sat_fm_lemmas                         false
% 11.51/1.94  --sat_fm_prep                           false
% 11.51/1.94  --sat_fm_uc_incr                        true
% 11.51/1.94  --sat_out_model                         small
% 11.51/1.94  --sat_out_clauses                       false
% 11.51/1.94  
% 11.51/1.94  ------ QBF Options
% 11.51/1.94  
% 11.51/1.94  --qbf_mode                              false
% 11.51/1.94  --qbf_elim_univ                         false
% 11.51/1.94  --qbf_dom_inst                          none
% 11.51/1.94  --qbf_dom_pre_inst                      false
% 11.51/1.94  --qbf_sk_in                             false
% 11.51/1.94  --qbf_pred_elim                         true
% 11.51/1.94  --qbf_split                             512
% 11.51/1.94  
% 11.51/1.94  ------ BMC1 Options
% 11.51/1.94  
% 11.51/1.94  --bmc1_incremental                      false
% 11.51/1.94  --bmc1_axioms                           reachable_all
% 11.51/1.94  --bmc1_min_bound                        0
% 11.51/1.94  --bmc1_max_bound                        -1
% 11.51/1.94  --bmc1_max_bound_default                -1
% 11.51/1.94  --bmc1_symbol_reachability              true
% 11.51/1.94  --bmc1_property_lemmas                  false
% 11.51/1.94  --bmc1_k_induction                      false
% 11.51/1.94  --bmc1_non_equiv_states                 false
% 11.51/1.94  --bmc1_deadlock                         false
% 11.51/1.94  --bmc1_ucm                              false
% 11.51/1.94  --bmc1_add_unsat_core                   none
% 11.51/1.94  --bmc1_unsat_core_children              false
% 11.51/1.94  --bmc1_unsat_core_extrapolate_axioms    false
% 11.51/1.94  --bmc1_out_stat                         full
% 11.51/1.94  --bmc1_ground_init                      false
% 11.51/1.94  --bmc1_pre_inst_next_state              false
% 11.51/1.94  --bmc1_pre_inst_state                   false
% 11.51/1.94  --bmc1_pre_inst_reach_state             false
% 11.51/1.94  --bmc1_out_unsat_core                   false
% 11.51/1.94  --bmc1_aig_witness_out                  false
% 11.51/1.94  --bmc1_verbose                          false
% 11.51/1.94  --bmc1_dump_clauses_tptp                false
% 11.51/1.94  --bmc1_dump_unsat_core_tptp             false
% 11.51/1.94  --bmc1_dump_file                        -
% 11.51/1.94  --bmc1_ucm_expand_uc_limit              128
% 11.51/1.94  --bmc1_ucm_n_expand_iterations          6
% 11.51/1.94  --bmc1_ucm_extend_mode                  1
% 11.51/1.94  --bmc1_ucm_init_mode                    2
% 11.51/1.94  --bmc1_ucm_cone_mode                    none
% 11.51/1.94  --bmc1_ucm_reduced_relation_type        0
% 11.51/1.94  --bmc1_ucm_relax_model                  4
% 11.51/1.94  --bmc1_ucm_full_tr_after_sat            true
% 11.51/1.94  --bmc1_ucm_expand_neg_assumptions       false
% 11.51/1.94  --bmc1_ucm_layered_model                none
% 11.51/1.94  --bmc1_ucm_max_lemma_size               10
% 11.51/1.94  
% 11.51/1.94  ------ AIG Options
% 11.51/1.94  
% 11.51/1.94  --aig_mode                              false
% 11.51/1.94  
% 11.51/1.94  ------ Instantiation Options
% 11.51/1.94  
% 11.51/1.94  --instantiation_flag                    true
% 11.51/1.94  --inst_sos_flag                         false
% 11.51/1.94  --inst_sos_phase                        true
% 11.51/1.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.51/1.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.51/1.94  --inst_lit_sel_side                     none
% 11.51/1.94  --inst_solver_per_active                1400
% 11.51/1.94  --inst_solver_calls_frac                1.
% 11.51/1.94  --inst_passive_queue_type               priority_queues
% 11.51/1.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.51/1.94  --inst_passive_queues_freq              [25;2]
% 11.51/1.94  --inst_dismatching                      true
% 11.51/1.94  --inst_eager_unprocessed_to_passive     true
% 11.51/1.94  --inst_prop_sim_given                   true
% 11.51/1.94  --inst_prop_sim_new                     false
% 11.51/1.94  --inst_subs_new                         false
% 11.51/1.94  --inst_eq_res_simp                      false
% 11.51/1.94  --inst_subs_given                       false
% 11.51/1.94  --inst_orphan_elimination               true
% 11.51/1.94  --inst_learning_loop_flag               true
% 11.51/1.94  --inst_learning_start                   3000
% 11.51/1.94  --inst_learning_factor                  2
% 11.51/1.94  --inst_start_prop_sim_after_learn       3
% 11.51/1.94  --inst_sel_renew                        solver
% 11.51/1.94  --inst_lit_activity_flag                true
% 11.51/1.94  --inst_restr_to_given                   false
% 11.51/1.94  --inst_activity_threshold               500
% 11.51/1.94  --inst_out_proof                        true
% 11.51/1.94  
% 11.51/1.94  ------ Resolution Options
% 11.51/1.94  
% 11.51/1.94  --resolution_flag                       false
% 11.51/1.94  --res_lit_sel                           adaptive
% 11.51/1.94  --res_lit_sel_side                      none
% 11.51/1.94  --res_ordering                          kbo
% 11.51/1.94  --res_to_prop_solver                    active
% 11.51/1.94  --res_prop_simpl_new                    false
% 11.51/1.94  --res_prop_simpl_given                  true
% 11.51/1.94  --res_passive_queue_type                priority_queues
% 11.51/1.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.51/1.94  --res_passive_queues_freq               [15;5]
% 11.51/1.94  --res_forward_subs                      full
% 11.51/1.94  --res_backward_subs                     full
% 11.51/1.94  --res_forward_subs_resolution           true
% 11.51/1.94  --res_backward_subs_resolution          true
% 11.51/1.94  --res_orphan_elimination                true
% 11.51/1.94  --res_time_limit                        2.
% 11.51/1.94  --res_out_proof                         true
% 11.51/1.94  
% 11.51/1.94  ------ Superposition Options
% 11.51/1.94  
% 11.51/1.94  --superposition_flag                    true
% 11.51/1.94  --sup_passive_queue_type                priority_queues
% 11.51/1.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.51/1.94  --sup_passive_queues_freq               [8;1;4]
% 11.51/1.94  --demod_completeness_check              fast
% 11.51/1.94  --demod_use_ground                      true
% 11.51/1.94  --sup_to_prop_solver                    passive
% 11.51/1.94  --sup_prop_simpl_new                    true
% 11.51/1.94  --sup_prop_simpl_given                  true
% 11.51/1.94  --sup_fun_splitting                     false
% 11.51/1.94  --sup_smt_interval                      50000
% 11.51/1.94  
% 11.51/1.94  ------ Superposition Simplification Setup
% 11.51/1.94  
% 11.51/1.94  --sup_indices_passive                   []
% 11.51/1.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.51/1.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.51/1.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.51/1.94  --sup_full_triv                         [TrivRules;PropSubs]
% 11.51/1.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.51/1.94  --sup_full_bw                           [BwDemod]
% 11.51/1.94  --sup_immed_triv                        [TrivRules]
% 11.51/1.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.51/1.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.51/1.94  --sup_immed_bw_main                     []
% 11.51/1.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.51/1.94  --sup_input_triv                        [Unflattening;TrivRules]
% 11.51/1.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.51/1.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.51/1.94  
% 11.51/1.94  ------ Combination Options
% 11.51/1.94  
% 11.51/1.94  --comb_res_mult                         3
% 11.51/1.94  --comb_sup_mult                         2
% 11.51/1.94  --comb_inst_mult                        10
% 11.51/1.94  
% 11.51/1.94  ------ Debug Options
% 11.51/1.94  
% 11.51/1.94  --dbg_backtrace                         false
% 11.51/1.94  --dbg_dump_prop_clauses                 false
% 11.51/1.94  --dbg_dump_prop_clauses_file            -
% 11.51/1.94  --dbg_out_stat                          false
% 11.51/1.94  
% 11.51/1.94  
% 11.51/1.94  
% 11.51/1.94  
% 11.51/1.94  ------ Proving...
% 11.51/1.94  
% 11.51/1.94  
% 11.51/1.94  % SZS status Theorem for theBenchmark.p
% 11.51/1.94  
% 11.51/1.94  % SZS output start CNFRefutation for theBenchmark.p
% 11.51/1.94  
% 11.51/1.94  fof(f4,axiom,(
% 11.51/1.94    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 11.51/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/1.94  
% 11.51/1.94  fof(f9,plain,(
% 11.51/1.94    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.51/1.94    inference(ennf_transformation,[],[f4])).
% 11.51/1.94  
% 11.51/1.94  fof(f41,plain,(
% 11.51/1.94    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.51/1.94    inference(cnf_transformation,[],[f9])).
% 11.51/1.94  
% 11.51/1.94  fof(f6,conjecture,(
% 11.51/1.94    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,X1) <=> (~r2_hidden(X4,X3) & r2_hidden(X4,X2)))) => k7_subset_1(X0,X2,X3) = X1))))),
% 11.51/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/1.94  
% 11.51/1.94  fof(f7,negated_conjecture,(
% 11.51/1.94    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,X1) <=> (~r2_hidden(X4,X3) & r2_hidden(X4,X2)))) => k7_subset_1(X0,X2,X3) = X1))))),
% 11.51/1.94    inference(negated_conjecture,[],[f6])).
% 11.51/1.94  
% 11.51/1.94  fof(f11,plain,(
% 11.51/1.94    ? [X0,X1] : (? [X2] : (? [X3] : ((k7_subset_1(X0,X2,X3) != X1 & ! [X4] : ((r2_hidden(X4,X1) <=> (~r2_hidden(X4,X3) & r2_hidden(X4,X2))) | ~m1_subset_1(X4,X0))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.51/1.94    inference(ennf_transformation,[],[f7])).
% 11.51/1.94  
% 11.51/1.94  fof(f12,plain,(
% 11.51/1.94    ? [X0,X1] : (? [X2] : (? [X3] : (k7_subset_1(X0,X2,X3) != X1 & ! [X4] : ((r2_hidden(X4,X1) <=> (~r2_hidden(X4,X3) & r2_hidden(X4,X2))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.51/1.94    inference(flattening,[],[f11])).
% 11.51/1.94  
% 11.51/1.94  fof(f23,plain,(
% 11.51/1.94    ? [X0,X1] : (? [X2] : (? [X3] : (k7_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | (r2_hidden(X4,X3) | ~r2_hidden(X4,X2))) & ((~r2_hidden(X4,X3) & r2_hidden(X4,X2)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.51/1.94    inference(nnf_transformation,[],[f12])).
% 11.51/1.94  
% 11.51/1.94  fof(f24,plain,(
% 11.51/1.94    ? [X0,X1] : (? [X2] : (? [X3] : (k7_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | r2_hidden(X4,X3) | ~r2_hidden(X4,X2)) & ((~r2_hidden(X4,X3) & r2_hidden(X4,X2)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.51/1.94    inference(flattening,[],[f23])).
% 11.51/1.94  
% 11.51/1.94  fof(f27,plain,(
% 11.51/1.94    ( ! [X2,X0,X1] : (? [X3] : (k7_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | r2_hidden(X4,X3) | ~r2_hidden(X4,X2)) & ((~r2_hidden(X4,X3) & r2_hidden(X4,X2)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (k7_subset_1(X0,X2,sK5) != X1 & ! [X4] : (((r2_hidden(X4,X1) | r2_hidden(X4,sK5) | ~r2_hidden(X4,X2)) & ((~r2_hidden(X4,sK5) & r2_hidden(X4,X2)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(sK5,k1_zfmisc_1(X0)))) )),
% 11.51/1.94    introduced(choice_axiom,[])).
% 11.51/1.94  
% 11.51/1.94  fof(f26,plain,(
% 11.51/1.94    ( ! [X0,X1] : (? [X2] : (? [X3] : (k7_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | r2_hidden(X4,X3) | ~r2_hidden(X4,X2)) & ((~r2_hidden(X4,X3) & r2_hidden(X4,X2)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (? [X3] : (k7_subset_1(X0,sK4,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | r2_hidden(X4,X3) | ~r2_hidden(X4,sK4)) & ((~r2_hidden(X4,X3) & r2_hidden(X4,sK4)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(sK4,k1_zfmisc_1(X0)))) )),
% 11.51/1.94    introduced(choice_axiom,[])).
% 11.51/1.94  
% 11.51/1.94  fof(f25,plain,(
% 11.51/1.94    ? [X0,X1] : (? [X2] : (? [X3] : (k7_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | r2_hidden(X4,X3) | ~r2_hidden(X4,X2)) & ((~r2_hidden(X4,X3) & r2_hidden(X4,X2)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (? [X3] : (k7_subset_1(sK2,X2,X3) != sK3 & ! [X4] : (((r2_hidden(X4,sK3) | r2_hidden(X4,X3) | ~r2_hidden(X4,X2)) & ((~r2_hidden(X4,X3) & r2_hidden(X4,X2)) | ~r2_hidden(X4,sK3))) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(sK2))) & m1_subset_1(X2,k1_zfmisc_1(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(sK2)))),
% 11.51/1.94    introduced(choice_axiom,[])).
% 11.51/1.94  
% 11.51/1.94  fof(f28,plain,(
% 11.51/1.94    ((k7_subset_1(sK2,sK4,sK5) != sK3 & ! [X4] : (((r2_hidden(X4,sK3) | r2_hidden(X4,sK5) | ~r2_hidden(X4,sK4)) & ((~r2_hidden(X4,sK5) & r2_hidden(X4,sK4)) | ~r2_hidden(X4,sK3))) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 11.51/1.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f27,f26,f25])).
% 11.51/1.94  
% 11.51/1.94  fof(f47,plain,(
% 11.51/1.94    ( ! [X4] : (~r2_hidden(X4,sK5) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,sK2)) )),
% 11.51/1.94    inference(cnf_transformation,[],[f28])).
% 11.51/1.94  
% 11.51/1.94  fof(f3,axiom,(
% 11.51/1.94    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.51/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/1.94  
% 11.51/1.94  fof(f8,plain,(
% 11.51/1.94    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.51/1.94    inference(ennf_transformation,[],[f3])).
% 11.51/1.94  
% 11.51/1.94  fof(f22,plain,(
% 11.51/1.94    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.51/1.94    inference(nnf_transformation,[],[f8])).
% 11.51/1.94  
% 11.51/1.94  fof(f38,plain,(
% 11.51/1.94    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 11.51/1.94    inference(cnf_transformation,[],[f22])).
% 11.51/1.94  
% 11.51/1.94  fof(f1,axiom,(
% 11.51/1.94    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 11.51/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/1.94  
% 11.51/1.94  fof(f13,plain,(
% 11.51/1.94    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 11.51/1.94    inference(nnf_transformation,[],[f1])).
% 11.51/1.94  
% 11.51/1.94  fof(f14,plain,(
% 11.51/1.94    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.51/1.94    inference(rectify,[],[f13])).
% 11.51/1.94  
% 11.51/1.94  fof(f15,plain,(
% 11.51/1.94    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 11.51/1.94    introduced(choice_axiom,[])).
% 11.51/1.94  
% 11.51/1.94  fof(f16,plain,(
% 11.51/1.94    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.51/1.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 11.51/1.94  
% 11.51/1.94  fof(f29,plain,(
% 11.51/1.94    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 11.51/1.94    inference(cnf_transformation,[],[f16])).
% 11.51/1.94  
% 11.51/1.94  fof(f2,axiom,(
% 11.51/1.94    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.51/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/1.94  
% 11.51/1.94  fof(f17,plain,(
% 11.51/1.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.51/1.94    inference(nnf_transformation,[],[f2])).
% 11.51/1.94  
% 11.51/1.94  fof(f18,plain,(
% 11.51/1.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.51/1.94    inference(flattening,[],[f17])).
% 11.51/1.94  
% 11.51/1.94  fof(f19,plain,(
% 11.51/1.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.51/1.94    inference(rectify,[],[f18])).
% 11.51/1.94  
% 11.51/1.94  fof(f20,plain,(
% 11.51/1.94    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 11.51/1.94    introduced(choice_axiom,[])).
% 11.51/1.94  
% 11.51/1.94  fof(f21,plain,(
% 11.51/1.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.51/1.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 11.51/1.94  
% 11.51/1.94  fof(f35,plain,(
% 11.51/1.94    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 11.51/1.94    inference(cnf_transformation,[],[f21])).
% 11.51/1.94  
% 11.51/1.94  fof(f46,plain,(
% 11.51/1.94    ( ! [X4] : (r2_hidden(X4,sK4) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,sK2)) )),
% 11.51/1.94    inference(cnf_transformation,[],[f28])).
% 11.51/1.94  
% 11.51/1.94  fof(f48,plain,(
% 11.51/1.94    ( ! [X4] : (r2_hidden(X4,sK3) | r2_hidden(X4,sK5) | ~r2_hidden(X4,sK4) | ~m1_subset_1(X4,sK2)) )),
% 11.51/1.94    inference(cnf_transformation,[],[f28])).
% 11.51/1.94  
% 11.51/1.94  fof(f34,plain,(
% 11.51/1.94    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 11.51/1.94    inference(cnf_transformation,[],[f21])).
% 11.51/1.94  
% 11.51/1.94  fof(f36,plain,(
% 11.51/1.94    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 11.51/1.94    inference(cnf_transformation,[],[f21])).
% 11.51/1.94  
% 11.51/1.94  fof(f44,plain,(
% 11.51/1.94    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 11.51/1.94    inference(cnf_transformation,[],[f28])).
% 11.51/1.94  
% 11.51/1.94  fof(f5,axiom,(
% 11.51/1.94    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 11.51/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/1.94  
% 11.51/1.94  fof(f10,plain,(
% 11.51/1.94    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.51/1.94    inference(ennf_transformation,[],[f5])).
% 11.51/1.94  
% 11.51/1.94  fof(f42,plain,(
% 11.51/1.94    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.51/1.94    inference(cnf_transformation,[],[f10])).
% 11.51/1.94  
% 11.51/1.94  fof(f49,plain,(
% 11.51/1.94    k7_subset_1(sK2,sK4,sK5) != sK3),
% 11.51/1.94    inference(cnf_transformation,[],[f28])).
% 11.51/1.94  
% 11.51/1.94  fof(f43,plain,(
% 11.51/1.94    m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 11.51/1.94    inference(cnf_transformation,[],[f28])).
% 11.51/1.94  
% 11.51/1.94  cnf(c_12,plain,
% 11.51/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.51/1.94      | ~ r2_hidden(X2,X0)
% 11.51/1.94      | r2_hidden(X2,X1) ),
% 11.51/1.94      inference(cnf_transformation,[],[f41]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_1634,plain,
% 11.51/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.51/1.94      | ~ r2_hidden(sK1(X0,X2,X3),X0)
% 11.51/1.94      | r2_hidden(sK1(X0,X2,X3),X1) ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_12]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_2424,plain,
% 11.51/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.51/1.94      | ~ r2_hidden(sK1(X0,X2,sK3),X0)
% 11.51/1.94      | r2_hidden(sK1(X0,X2,sK3),X1) ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_1634]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_4936,plain,
% 11.51/1.94      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 11.51/1.94      | ~ r2_hidden(sK1(sK4,X0,sK3),sK4)
% 11.51/1.94      | r2_hidden(sK1(sK4,X0,sK3),sK2) ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_2424]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_30225,plain,
% 11.51/1.94      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 11.51/1.94      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK4)
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK2) ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_4936]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_30228,plain,
% 11.51/1.94      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK4) != iProver_top
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK2) = iProver_top ),
% 11.51/1.94      inference(predicate_to_equality,[status(thm)],[c_30225]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_16,negated_conjecture,
% 11.51/1.94      ( ~ m1_subset_1(X0,sK2)
% 11.51/1.94      | ~ r2_hidden(X0,sK3)
% 11.51/1.94      | ~ r2_hidden(X0,sK5) ),
% 11.51/1.94      inference(cnf_transformation,[],[f47]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_1597,plain,
% 11.51/1.94      ( ~ m1_subset_1(sK1(X0,X1,sK3),sK2)
% 11.51/1.94      | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
% 11.51/1.94      | ~ r2_hidden(sK1(X0,X1,sK3),sK5) ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_16]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_2894,plain,
% 11.51/1.94      ( ~ m1_subset_1(sK1(X0,sK5,sK3),sK2)
% 11.51/1.94      | ~ r2_hidden(sK1(X0,sK5,sK3),sK3)
% 11.51/1.94      | ~ r2_hidden(sK1(X0,sK5,sK3),sK5) ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_1597]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_21185,plain,
% 11.51/1.94      ( ~ m1_subset_1(sK1(sK4,sK5,sK3),sK2)
% 11.51/1.94      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 11.51/1.94      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK5) ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_2894]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_21188,plain,
% 11.51/1.94      ( m1_subset_1(sK1(sK4,sK5,sK3),sK2) != iProver_top
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK5) != iProver_top ),
% 11.51/1.94      inference(predicate_to_equality,[status(thm)],[c_21185]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_10,plain,
% 11.51/1.94      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.51/1.94      inference(cnf_transformation,[],[f38]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_1,plain,
% 11.51/1.94      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 11.51/1.94      inference(cnf_transformation,[],[f29]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_115,plain,
% 11.51/1.94      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 11.51/1.94      inference(global_propositional_subsumption,
% 11.51/1.94                [status(thm)],
% 11.51/1.94                [c_10,c_1]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_116,plain,
% 11.51/1.94      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 11.51/1.94      inference(renaming,[status(thm)],[c_115]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_1695,plain,
% 11.51/1.94      ( m1_subset_1(sK1(X0,X1,sK3),sK2)
% 11.51/1.94      | ~ r2_hidden(sK1(X0,X1,sK3),sK2) ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_116]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_2858,plain,
% 11.51/1.94      ( m1_subset_1(sK1(sK4,X0,sK3),sK2)
% 11.51/1.94      | ~ r2_hidden(sK1(sK4,X0,sK3),sK2) ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_1695]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_21183,plain,
% 11.51/1.94      ( m1_subset_1(sK1(sK4,sK5,sK3),sK2)
% 11.51/1.94      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK2) ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_2858]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_21186,plain,
% 11.51/1.94      ( m1_subset_1(sK1(sK4,sK5,sK3),sK2) = iProver_top
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK2) != iProver_top ),
% 11.51/1.94      inference(predicate_to_equality,[status(thm)],[c_21183]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_3,plain,
% 11.51/1.94      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 11.51/1.94      | r2_hidden(sK1(X0,X1,X2),X2)
% 11.51/1.94      | k4_xboole_0(X0,X1) = X2 ),
% 11.51/1.94      inference(cnf_transformation,[],[f35]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_1348,plain,
% 11.51/1.94      ( ~ r2_hidden(sK1(X0,X1,sK3),X1)
% 11.51/1.94      | r2_hidden(sK1(X0,X1,sK3),sK3)
% 11.51/1.94      | k4_xboole_0(X0,X1) = sK3 ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_3]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_5385,plain,
% 11.51/1.94      ( r2_hidden(sK1(X0,sK5,sK3),sK3)
% 11.51/1.94      | ~ r2_hidden(sK1(X0,sK5,sK3),sK5)
% 11.51/1.94      | k4_xboole_0(X0,sK5) = sK3 ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_1348]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_15962,plain,
% 11.51/1.94      ( r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 11.51/1.94      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK5)
% 11.51/1.94      | k4_xboole_0(sK4,sK5) = sK3 ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_5385]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_15963,plain,
% 11.51/1.94      ( k4_xboole_0(sK4,sK5) = sK3
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK3) = iProver_top
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK5) != iProver_top ),
% 11.51/1.94      inference(predicate_to_equality,[status(thm)],[c_15962]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_1591,plain,
% 11.51/1.94      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 11.51/1.94      | r2_hidden(sK1(X1,X2,sK3),X0)
% 11.51/1.94      | ~ r2_hidden(sK1(X1,X2,sK3),sK3) ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_12]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_4913,plain,
% 11.51/1.94      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
% 11.51/1.94      | ~ r2_hidden(sK1(sK4,X0,sK3),sK3)
% 11.51/1.94      | r2_hidden(sK1(sK4,X0,sK3),sK2) ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_1591]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_12696,plain,
% 11.51/1.94      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
% 11.51/1.94      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK2) ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_4913]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_12697,plain,
% 11.51/1.94      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK2) = iProver_top ),
% 11.51/1.94      inference(predicate_to_equality,[status(thm)],[c_12696]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_17,negated_conjecture,
% 11.51/1.94      ( ~ m1_subset_1(X0,sK2) | ~ r2_hidden(X0,sK3) | r2_hidden(X0,sK4) ),
% 11.51/1.94      inference(cnf_transformation,[],[f46]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_1596,plain,
% 11.51/1.94      ( ~ m1_subset_1(sK1(X0,X1,sK3),sK2)
% 11.51/1.94      | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
% 11.51/1.94      | r2_hidden(sK1(X0,X1,sK3),sK4) ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_17]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_12271,plain,
% 11.51/1.94      ( ~ m1_subset_1(sK1(sK4,sK5,sK3),sK2)
% 11.51/1.94      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK4) ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_1596]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_12275,plain,
% 11.51/1.94      ( m1_subset_1(sK1(sK4,sK5,sK3),sK2) != iProver_top
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK4) = iProver_top ),
% 11.51/1.94      inference(predicate_to_equality,[status(thm)],[c_12271]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_15,negated_conjecture,
% 11.51/1.94      ( ~ m1_subset_1(X0,sK2)
% 11.51/1.94      | r2_hidden(X0,sK3)
% 11.51/1.94      | r2_hidden(X0,sK5)
% 11.51/1.94      | ~ r2_hidden(X0,sK4) ),
% 11.51/1.94      inference(cnf_transformation,[],[f48]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_1638,plain,
% 11.51/1.94      ( ~ m1_subset_1(sK1(sK4,X0,X1),sK2)
% 11.51/1.94      | r2_hidden(sK1(sK4,X0,X1),sK3)
% 11.51/1.94      | r2_hidden(sK1(sK4,X0,X1),sK5)
% 11.51/1.94      | ~ r2_hidden(sK1(sK4,X0,X1),sK4) ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_15]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_2859,plain,
% 11.51/1.94      ( ~ m1_subset_1(sK1(sK4,X0,sK3),sK2)
% 11.51/1.94      | r2_hidden(sK1(sK4,X0,sK3),sK3)
% 11.51/1.94      | r2_hidden(sK1(sK4,X0,sK3),sK5)
% 11.51/1.94      | ~ r2_hidden(sK1(sK4,X0,sK3),sK4) ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_1638]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_5419,plain,
% 11.51/1.94      ( ~ m1_subset_1(sK1(sK4,sK5,sK3),sK2)
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK5)
% 11.51/1.94      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK4) ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_2859]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_5425,plain,
% 11.51/1.94      ( m1_subset_1(sK1(sK4,sK5,sK3),sK2) != iProver_top
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK3) = iProver_top
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK5) = iProver_top
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK4) != iProver_top ),
% 11.51/1.94      inference(predicate_to_equality,[status(thm)],[c_5419]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_4,plain,
% 11.51/1.94      ( r2_hidden(sK1(X0,X1,X2),X0)
% 11.51/1.94      | r2_hidden(sK1(X0,X1,X2),X2)
% 11.51/1.94      | k4_xboole_0(X0,X1) = X2 ),
% 11.51/1.94      inference(cnf_transformation,[],[f34]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_1637,plain,
% 11.51/1.94      ( r2_hidden(sK1(sK4,X0,X1),X1)
% 11.51/1.94      | r2_hidden(sK1(sK4,X0,X1),sK4)
% 11.51/1.94      | k4_xboole_0(sK4,X0) = X1 ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_4]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_1737,plain,
% 11.51/1.94      ( r2_hidden(sK1(sK4,X0,sK3),sK3)
% 11.51/1.94      | r2_hidden(sK1(sK4,X0,sK3),sK4)
% 11.51/1.94      | k4_xboole_0(sK4,X0) = sK3 ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_1637]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_5420,plain,
% 11.51/1.94      ( r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK4)
% 11.51/1.94      | k4_xboole_0(sK4,sK5) = sK3 ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_1737]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_5423,plain,
% 11.51/1.94      ( k4_xboole_0(sK4,sK5) = sK3
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK3) = iProver_top
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK4) = iProver_top ),
% 11.51/1.94      inference(predicate_to_equality,[status(thm)],[c_5420]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_2,plain,
% 11.51/1.94      ( ~ r2_hidden(sK1(X0,X1,X2),X0)
% 11.51/1.94      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 11.51/1.94      | r2_hidden(sK1(X0,X1,X2),X1)
% 11.51/1.94      | k4_xboole_0(X0,X1) = X2 ),
% 11.51/1.94      inference(cnf_transformation,[],[f36]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_1346,plain,
% 11.51/1.94      ( ~ r2_hidden(sK1(X0,X1,sK3),X0)
% 11.51/1.94      | r2_hidden(sK1(X0,X1,sK3),X1)
% 11.51/1.94      | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
% 11.51/1.94      | k4_xboole_0(X0,X1) = sK3 ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_2]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_2895,plain,
% 11.51/1.94      ( ~ r2_hidden(sK1(X0,sK5,sK3),X0)
% 11.51/1.94      | ~ r2_hidden(sK1(X0,sK5,sK3),sK3)
% 11.51/1.94      | r2_hidden(sK1(X0,sK5,sK3),sK5)
% 11.51/1.94      | k4_xboole_0(X0,sK5) = sK3 ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_1346]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_5418,plain,
% 11.51/1.94      ( ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK5)
% 11.51/1.94      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK4)
% 11.51/1.94      | k4_xboole_0(sK4,sK5) = sK3 ),
% 11.51/1.94      inference(instantiation,[status(thm)],[c_2895]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_5421,plain,
% 11.51/1.94      ( k4_xboole_0(sK4,sK5) = sK3
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK3) != iProver_top
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK5) = iProver_top
% 11.51/1.94      | r2_hidden(sK1(sK4,sK5,sK3),sK4) != iProver_top ),
% 11.51/1.94      inference(predicate_to_equality,[status(thm)],[c_5418]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_19,negated_conjecture,
% 11.51/1.94      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 11.51/1.94      inference(cnf_transformation,[],[f44]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_1059,plain,
% 11.51/1.94      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 11.51/1.94      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_13,plain,
% 11.51/1.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.51/1.94      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 11.51/1.94      inference(cnf_transformation,[],[f42]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_1064,plain,
% 11.51/1.94      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 11.51/1.94      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.51/1.94      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_1375,plain,
% 11.51/1.94      ( k7_subset_1(sK2,sK4,X0) = k4_xboole_0(sK4,X0) ),
% 11.51/1.94      inference(superposition,[status(thm)],[c_1059,c_1064]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_14,negated_conjecture,
% 11.51/1.94      ( k7_subset_1(sK2,sK4,sK5) != sK3 ),
% 11.51/1.94      inference(cnf_transformation,[],[f49]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_1553,plain,
% 11.51/1.94      ( k4_xboole_0(sK4,sK5) != sK3 ),
% 11.51/1.94      inference(demodulation,[status(thm)],[c_1375,c_14]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_22,plain,
% 11.51/1.94      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 11.51/1.94      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_20,negated_conjecture,
% 11.51/1.94      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
% 11.51/1.94      inference(cnf_transformation,[],[f43]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(c_21,plain,
% 11.51/1.94      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
% 11.51/1.94      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.51/1.94  
% 11.51/1.94  cnf(contradiction,plain,
% 11.51/1.94      ( $false ),
% 11.51/1.94      inference(minisat,
% 11.51/1.94                [status(thm)],
% 11.51/1.94                [c_30228,c_21188,c_21186,c_15963,c_12697,c_12275,c_5425,
% 11.51/1.94                 c_5423,c_5421,c_1553,c_22,c_21]) ).
% 11.51/1.94  
% 11.51/1.94  
% 11.51/1.94  % SZS output end CNFRefutation for theBenchmark.p
% 11.51/1.94  
% 11.51/1.94  ------                               Statistics
% 11.51/1.94  
% 11.51/1.94  ------ General
% 11.51/1.94  
% 11.51/1.94  abstr_ref_over_cycles:                  0
% 11.51/1.94  abstr_ref_under_cycles:                 0
% 11.51/1.94  gc_basic_clause_elim:                   0
% 11.51/1.94  forced_gc_time:                         0
% 11.51/1.94  parsing_time:                           0.009
% 11.51/1.94  unif_index_cands_time:                  0.
% 11.51/1.94  unif_index_add_time:                    0.
% 11.51/1.94  orderings_time:                         0.
% 11.51/1.94  out_proof_time:                         0.011
% 11.51/1.94  total_time:                             1.1
% 11.51/1.94  num_of_symbols:                         43
% 11.51/1.94  num_of_terms:                           38357
% 11.51/1.94  
% 11.51/1.94  ------ Preprocessing
% 11.51/1.94  
% 11.51/1.94  num_of_splits:                          0
% 11.51/1.94  num_of_split_atoms:                     0
% 11.51/1.94  num_of_reused_defs:                     0
% 11.51/1.94  num_eq_ax_congr_red:                    14
% 11.51/1.94  num_of_sem_filtered_clauses:            1
% 11.51/1.94  num_of_subtypes:                        0
% 11.51/1.94  monotx_restored_types:                  0
% 11.51/1.94  sat_num_of_epr_types:                   0
% 11.51/1.94  sat_num_of_non_cyclic_types:            0
% 11.51/1.94  sat_guarded_non_collapsed_types:        0
% 11.51/1.94  num_pure_diseq_elim:                    0
% 11.51/1.94  simp_replaced_by:                       0
% 11.51/1.94  res_preprocessed:                       76
% 11.51/1.94  prep_upred:                             0
% 11.51/1.94  prep_unflattend:                        47
% 11.51/1.94  smt_new_axioms:                         0
% 11.51/1.94  pred_elim_cands:                        3
% 11.51/1.94  pred_elim:                              0
% 11.51/1.94  pred_elim_cl:                           0
% 11.51/1.94  pred_elim_cycles:                       1
% 11.51/1.94  merged_defs:                            0
% 11.51/1.94  merged_defs_ncl:                        0
% 11.51/1.94  bin_hyper_res:                          0
% 11.51/1.94  prep_cycles:                            3
% 11.51/1.94  pred_elim_time:                         0.007
% 11.51/1.94  splitting_time:                         0.
% 11.51/1.94  sem_filter_time:                        0.
% 11.51/1.94  monotx_time:                            0.
% 11.51/1.94  subtype_inf_time:                       0.
% 11.51/1.94  
% 11.51/1.94  ------ Problem properties
% 11.51/1.94  
% 11.51/1.94  clauses:                                21
% 11.51/1.94  conjectures:                            7
% 11.51/1.94  epr:                                    8
% 11.51/1.94  horn:                                   14
% 11.51/1.94  ground:                                 4
% 11.51/1.94  unary:                                  4
% 11.51/1.94  binary:                                 6
% 11.51/1.94  lits:                                   51
% 11.51/1.94  lits_eq:                                5
% 11.51/1.94  fd_pure:                                0
% 11.51/1.94  fd_pseudo:                              0
% 11.51/1.94  fd_cond:                                0
% 11.51/1.94  fd_pseudo_cond:                         3
% 11.51/1.94  ac_symbols:                             0
% 11.51/1.94  
% 11.51/1.94  ------ Propositional Solver
% 11.51/1.94  
% 11.51/1.94  prop_solver_calls:                      29
% 11.51/1.94  prop_fast_solver_calls:                 1169
% 11.51/1.94  smt_solver_calls:                       0
% 11.51/1.94  smt_fast_solver_calls:                  0
% 11.51/1.94  prop_num_of_clauses:                    13583
% 11.51/1.94  prop_preprocess_simplified:             29730
% 11.51/1.94  prop_fo_subsumed:                       15
% 11.51/1.94  prop_solver_time:                       0.
% 11.51/1.94  smt_solver_time:                        0.
% 11.51/1.94  smt_fast_solver_time:                   0.
% 11.51/1.94  prop_fast_solver_time:                  0.
% 11.51/1.94  prop_unsat_core_time:                   0.003
% 11.51/1.94  
% 11.51/1.94  ------ QBF
% 11.51/1.94  
% 11.51/1.94  qbf_q_res:                              0
% 11.51/1.94  qbf_num_tautologies:                    0
% 11.51/1.94  qbf_prep_cycles:                        0
% 11.51/1.94  
% 11.51/1.94  ------ BMC1
% 11.51/1.94  
% 11.51/1.94  bmc1_current_bound:                     -1
% 11.51/1.94  bmc1_last_solved_bound:                 -1
% 11.51/1.94  bmc1_unsat_core_size:                   -1
% 11.51/1.94  bmc1_unsat_core_parents_size:           -1
% 11.51/1.94  bmc1_merge_next_fun:                    0
% 11.51/1.94  bmc1_unsat_core_clauses_time:           0.
% 11.51/1.94  
% 11.51/1.94  ------ Instantiation
% 11.51/1.94  
% 11.51/1.94  inst_num_of_clauses:                    3760
% 11.51/1.94  inst_num_in_passive:                    745
% 11.51/1.94  inst_num_in_active:                     1133
% 11.51/1.94  inst_num_in_unprocessed:                1885
% 11.51/1.94  inst_num_of_loops:                      1406
% 11.51/1.94  inst_num_of_learning_restarts:          0
% 11.51/1.94  inst_num_moves_active_passive:          267
% 11.51/1.94  inst_lit_activity:                      0
% 11.51/1.94  inst_lit_activity_moves:                0
% 11.51/1.94  inst_num_tautologies:                   0
% 11.51/1.94  inst_num_prop_implied:                  0
% 11.51/1.94  inst_num_existing_simplified:           0
% 11.51/1.94  inst_num_eq_res_simplified:             0
% 11.51/1.94  inst_num_child_elim:                    0
% 11.51/1.94  inst_num_of_dismatching_blockings:      7794
% 11.51/1.94  inst_num_of_non_proper_insts:           5144
% 11.51/1.94  inst_num_of_duplicates:                 0
% 11.51/1.94  inst_inst_num_from_inst_to_res:         0
% 11.51/1.94  inst_dismatching_checking_time:         0.
% 11.51/1.94  
% 11.51/1.94  ------ Resolution
% 11.51/1.94  
% 11.51/1.94  res_num_of_clauses:                     0
% 11.51/1.94  res_num_in_passive:                     0
% 11.51/1.94  res_num_in_active:                      0
% 11.51/1.94  res_num_of_loops:                       79
% 11.51/1.94  res_forward_subset_subsumed:            148
% 11.51/1.94  res_backward_subset_subsumed:           6
% 11.51/1.94  res_forward_subsumed:                   1
% 11.51/1.94  res_backward_subsumed:                  0
% 11.51/1.94  res_forward_subsumption_resolution:     0
% 11.51/1.94  res_backward_subsumption_resolution:    0
% 11.51/1.94  res_clause_to_clause_subsumption:       6708
% 11.51/1.94  res_orphan_elimination:                 0
% 11.51/1.94  res_tautology_del:                      1391
% 11.51/1.94  res_num_eq_res_simplified:              0
% 11.51/1.94  res_num_sel_changes:                    0
% 11.51/1.94  res_moves_from_active_to_pass:          0
% 11.51/1.94  
% 11.51/1.94  ------ Superposition
% 11.51/1.94  
% 11.51/1.94  sup_time_total:                         0.
% 11.51/1.94  sup_time_generating:                    0.
% 11.51/1.94  sup_time_sim_full:                      0.
% 11.51/1.94  sup_time_sim_immed:                     0.
% 11.51/1.94  
% 11.51/1.94  sup_num_of_clauses:                     907
% 11.51/1.94  sup_num_in_active:                      272
% 11.51/1.94  sup_num_in_passive:                     635
% 11.51/1.94  sup_num_of_loops:                       280
% 11.51/1.94  sup_fw_superposition:                   464
% 11.51/1.94  sup_bw_superposition:                   1265
% 11.51/1.94  sup_immediate_simplified:               674
% 11.51/1.94  sup_given_eliminated:                   6
% 11.51/1.94  comparisons_done:                       0
% 11.51/1.94  comparisons_avoided:                    0
% 11.51/1.94  
% 11.51/1.94  ------ Simplifications
% 11.51/1.94  
% 11.51/1.94  
% 11.51/1.94  sim_fw_subset_subsumed:                 81
% 11.51/1.94  sim_bw_subset_subsumed:                 7
% 11.51/1.94  sim_fw_subsumed:                        476
% 11.51/1.94  sim_bw_subsumed:                        59
% 11.51/1.94  sim_fw_subsumption_res:                 24
% 11.51/1.94  sim_bw_subsumption_res:                 0
% 11.51/1.94  sim_tautology_del:                      45
% 11.51/1.94  sim_eq_tautology_del:                   5
% 11.51/1.94  sim_eq_res_simp:                        25
% 11.51/1.94  sim_fw_demodulated:                     8
% 11.51/1.94  sim_bw_demodulated:                     8
% 11.51/1.94  sim_light_normalised:                   53
% 11.51/1.94  sim_joinable_taut:                      0
% 11.51/1.94  sim_joinable_simp:                      0
% 11.51/1.94  sim_ac_normalised:                      0
% 11.51/1.94  sim_smt_subsumption:                    0
% 11.51/1.94  
%------------------------------------------------------------------------------

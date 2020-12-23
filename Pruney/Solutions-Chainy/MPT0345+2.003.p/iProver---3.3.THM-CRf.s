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
% DateTime   : Thu Dec  3 11:39:02 EST 2020

% Result     : Theorem 11.72s
% Output     : CNFRefutation 11.72s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 580 expanded)
%              Number of clauses        :   54 ( 140 expanded)
%              Number of leaves         :   13 ( 159 expanded)
%              Depth                    :   15
%              Number of atoms          :  418 (4715 expanded)
%              Number of equality atoms :   73 ( 585 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   22 (   2 average)
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

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

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
                    <=> ( r2_hidden(X4,X3)
                        | r2_hidden(X4,X2) ) ) )
               => k4_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
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
                      <=> ( r2_hidden(X4,X3)
                          | r2_hidden(X4,X2) ) ) )
                 => k4_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ( ~ r2_hidden(X4,X3)
                        & ~ r2_hidden(X4,X2) ) )
                    & ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2)
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ( ~ r2_hidden(X4,X3)
                        & ~ r2_hidden(X4,X2) ) )
                    & ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2)
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k4_subset_1(X0,X2,X3) != X1
          & ! [X4] :
              ( ( ( r2_hidden(X4,X1)
                  | ( ~ r2_hidden(X4,X3)
                    & ~ r2_hidden(X4,X2) ) )
                & ( r2_hidden(X4,X3)
                  | r2_hidden(X4,X2)
                  | ~ r2_hidden(X4,X1) ) )
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( k4_subset_1(X0,X2,sK5) != X1
        & ! [X4] :
            ( ( ( r2_hidden(X4,X1)
                | ( ~ r2_hidden(X4,sK5)
                  & ~ r2_hidden(X4,X2) ) )
              & ( r2_hidden(X4,sK5)
                | r2_hidden(X4,X2)
                | ~ r2_hidden(X4,X1) ) )
            | ~ m1_subset_1(X4,X0) )
        & m1_subset_1(sK5,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ( ~ r2_hidden(X4,X3)
                        & ~ r2_hidden(X4,X2) ) )
                    & ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2)
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ? [X3] :
            ( k4_subset_1(X0,sK4,X3) != X1
            & ! [X4] :
                ( ( ( r2_hidden(X4,X1)
                    | ( ~ r2_hidden(X4,X3)
                      & ~ r2_hidden(X4,sK4) ) )
                  & ( r2_hidden(X4,X3)
                    | r2_hidden(X4,sK4)
                    | ~ r2_hidden(X4,X1) ) )
                | ~ m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(X0)) )
        & m1_subset_1(sK4,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k4_subset_1(X0,X2,X3) != X1
                & ! [X4] :
                    ( ( ( r2_hidden(X4,X1)
                        | ( ~ r2_hidden(X4,X3)
                          & ~ r2_hidden(X4,X2) ) )
                      & ( r2_hidden(X4,X3)
                        | r2_hidden(X4,X2)
                        | ~ r2_hidden(X4,X1) ) )
                    | ~ m1_subset_1(X4,X0) )
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(sK2,X2,X3) != sK3
              & ! [X4] :
                  ( ( ( r2_hidden(X4,sK3)
                      | ( ~ r2_hidden(X4,X3)
                        & ~ r2_hidden(X4,X2) ) )
                    & ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2)
                      | ~ r2_hidden(X4,sK3) ) )
                  | ~ m1_subset_1(X4,sK2) )
              & m1_subset_1(X3,k1_zfmisc_1(sK2)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k4_subset_1(sK2,sK4,sK5) != sK3
    & ! [X4] :
        ( ( ( r2_hidden(X4,sK3)
            | ( ~ r2_hidden(X4,sK5)
              & ~ r2_hidden(X4,sK4) ) )
          & ( r2_hidden(X4,sK5)
            | r2_hidden(X4,sK4)
            | ~ r2_hidden(X4,sK3) ) )
        | ~ m1_subset_1(X4,sK2) )
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f28,f27,f26])).

fof(f50,plain,(
    k4_subset_1(sK2,sK4,sK5) != sK3 ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X4] :
      ( r2_hidden(X4,sK3)
      | ~ r2_hidden(X4,sK5)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X4] :
      ( r2_hidden(X4,sK3)
      | ~ r2_hidden(X4,sK4)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f29])).

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
    inference(nnf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f30,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X4] :
      ( r2_hidden(X4,sK5)
      | r2_hidden(X4,sK4)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_187,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_186,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1852,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_187,c_186])).

cnf(c_2982,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X0)
    | X2 = k2_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_4,c_1852])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1939,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X3 != k2_xboole_0(X0,X2)
    | k4_subset_1(X1,X0,X2) = X3 ),
    inference(resolution,[status(thm)],[c_13,c_187])).

cnf(c_14,negated_conjecture,
    ( k4_subset_1(sK2,sK4,sK5) != sK3 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_6160,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | sK3 != k2_xboole_0(sK4,sK5) ),
    inference(resolution,[status(thm)],[c_1939,c_14])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_722,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | k4_subset_1(sK2,X0,sK5) = k2_xboole_0(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_749,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | k4_subset_1(sK2,sK4,sK5) = k2_xboole_0(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_692,plain,
    ( k4_subset_1(sK2,sK4,sK5) != X0
    | k4_subset_1(sK2,sK4,sK5) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_187])).

cnf(c_1053,plain,
    ( k4_subset_1(sK2,sK4,sK5) != k2_xboole_0(X0,X1)
    | k4_subset_1(sK2,sK4,sK5) = sK3
    | sK3 != k2_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_1165,plain,
    ( k4_subset_1(sK2,sK4,sK5) != k2_xboole_0(sK4,sK5)
    | k4_subset_1(sK2,sK4,sK5) = sK3
    | sK3 != k2_xboole_0(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_6661,plain,
    ( sK3 != k2_xboole_0(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6160,c_19,c_18,c_14,c_749,c_1165])).

cnf(c_38883,plain,
    ( r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | r2_hidden(sK1(sK4,sK5,sK3),sK5)
    | r2_hidden(sK1(sK4,sK5,sK3),sK4) ),
    inference(resolution,[status(thm)],[c_2982,c_6661])).

cnf(c_15,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK5) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3526,plain,
    ( ~ m1_subset_1(sK1(sK4,sK5,sK3),sK2)
    | r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_495,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_494,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_499,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1244,plain,
    ( k4_subset_1(sK2,sK4,X0) = k2_xboole_0(sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_494,c_499])).

cnf(c_4258,plain,
    ( k4_subset_1(sK2,sK4,sK5) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_495,c_1244])).

cnf(c_4649,plain,
    ( k2_xboole_0(sK4,sK5) != sK3 ),
    inference(demodulation,[status(thm)],[c_4258,c_14])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1430,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(X0,sK2) ),
    inference(resolution,[status(thm)],[c_12,c_19])).

cnf(c_3008,plain,
    ( r2_hidden(sK1(sK4,X0,X1),X0)
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | r2_hidden(sK1(sK4,X0,X1),sK2)
    | k2_xboole_0(sK4,X0) = X1 ),
    inference(resolution,[status(thm)],[c_4,c_1430])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1432,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(X0,sK2) ),
    inference(resolution,[status(thm)],[c_12,c_20])).

cnf(c_13784,plain,
    ( r2_hidden(sK1(sK4,X0,sK3),X0)
    | r2_hidden(sK1(sK4,X0,sK3),sK2)
    | k2_xboole_0(sK4,X0) = sK3 ),
    inference(resolution,[status(thm)],[c_3008,c_1432])).

cnf(c_1428,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(X0,sK2) ),
    inference(resolution,[status(thm)],[c_12,c_18])).

cnf(c_14942,plain,
    ( r2_hidden(sK1(sK4,sK5,sK3),sK2)
    | k2_xboole_0(sK4,sK5) = sK3 ),
    inference(resolution,[status(thm)],[c_13784,c_1428])).

cnf(c_16,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1490,plain,
    ( ~ m1_subset_1(sK1(sK4,X0,sK3),sK2)
    | r2_hidden(sK1(sK4,X0,sK3),sK3)
    | ~ r2_hidden(sK1(sK4,X0,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_29303,plain,
    ( ~ m1_subset_1(sK1(sK4,sK5,sK3),sK2)
    | r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1490])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_150,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_1])).

cnf(c_151,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_150])).

cnf(c_38008,plain,
    ( m1_subset_1(sK1(sK4,sK5,sK3),sK2)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_151])).

cnf(c_41110,plain,
    ( r2_hidden(sK1(sK4,sK5,sK3),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_38883,c_3526,c_4649,c_14942,c_29303,c_38008])).

cnf(c_17,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,sK3)
    | r2_hidden(X0,sK5)
    | r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_872,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(X0,sK5)
    | r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,sK2) ),
    inference(resolution,[status(thm)],[c_17,c_151])).

cnf(c_1594,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(X0,sK5)
    | r2_hidden(X0,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1432,c_872])).

cnf(c_41129,plain,
    ( r2_hidden(sK1(sK4,sK5,sK3),sK5)
    | r2_hidden(sK1(sK4,sK5,sK3),sK4) ),
    inference(resolution,[status(thm)],[c_41110,c_1594])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_922,plain,
    ( ~ r2_hidden(sK1(X0,X1,sK3),X1)
    | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
    | k2_xboole_0(X0,X1) = sK3 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5617,plain,
    ( ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK5)
    | k2_xboole_0(sK4,sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_922])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X2)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_921,plain,
    ( ~ r2_hidden(sK1(X0,X1,sK3),X0)
    | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
    | k2_xboole_0(X0,X1) = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5618,plain,
    ( ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK4)
    | k2_xboole_0(sK4,sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_921])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_41129,c_41110,c_5617,c_5618,c_4649])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:25:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.72/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.72/1.99  
% 11.72/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.72/1.99  
% 11.72/1.99  ------  iProver source info
% 11.72/1.99  
% 11.72/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.72/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.72/1.99  git: non_committed_changes: false
% 11.72/1.99  git: last_make_outside_of_git: false
% 11.72/1.99  
% 11.72/1.99  ------ 
% 11.72/1.99  
% 11.72/1.99  ------ Input Options
% 11.72/1.99  
% 11.72/1.99  --out_options                           all
% 11.72/1.99  --tptp_safe_out                         true
% 11.72/1.99  --problem_path                          ""
% 11.72/1.99  --include_path                          ""
% 11.72/1.99  --clausifier                            res/vclausify_rel
% 11.72/1.99  --clausifier_options                    --mode clausify
% 11.72/1.99  --stdin                                 false
% 11.72/1.99  --stats_out                             sel
% 11.72/1.99  
% 11.72/1.99  ------ General Options
% 11.72/1.99  
% 11.72/1.99  --fof                                   false
% 11.72/1.99  --time_out_real                         604.99
% 11.72/1.99  --time_out_virtual                      -1.
% 11.72/1.99  --symbol_type_check                     false
% 11.72/1.99  --clausify_out                          false
% 11.72/1.99  --sig_cnt_out                           false
% 11.72/1.99  --trig_cnt_out                          false
% 11.72/1.99  --trig_cnt_out_tolerance                1.
% 11.72/1.99  --trig_cnt_out_sk_spl                   false
% 11.72/1.99  --abstr_cl_out                          false
% 11.72/1.99  
% 11.72/1.99  ------ Global Options
% 11.72/1.99  
% 11.72/1.99  --schedule                              none
% 11.72/1.99  --add_important_lit                     false
% 11.72/1.99  --prop_solver_per_cl                    1000
% 11.72/1.99  --min_unsat_core                        false
% 11.72/1.99  --soft_assumptions                      false
% 11.72/1.99  --soft_lemma_size                       3
% 11.72/1.99  --prop_impl_unit_size                   0
% 11.72/1.99  --prop_impl_unit                        []
% 11.72/1.99  --share_sel_clauses                     true
% 11.72/1.99  --reset_solvers                         false
% 11.72/1.99  --bc_imp_inh                            [conj_cone]
% 11.72/1.99  --conj_cone_tolerance                   3.
% 11.72/1.99  --extra_neg_conj                        none
% 11.72/1.99  --large_theory_mode                     true
% 11.72/1.99  --prolific_symb_bound                   200
% 11.72/1.99  --lt_threshold                          2000
% 11.72/1.99  --clause_weak_htbl                      true
% 11.72/1.99  --gc_record_bc_elim                     false
% 11.72/1.99  
% 11.72/1.99  ------ Preprocessing Options
% 11.72/1.99  
% 11.72/1.99  --preprocessing_flag                    true
% 11.72/1.99  --time_out_prep_mult                    0.1
% 11.72/1.99  --splitting_mode                        input
% 11.72/1.99  --splitting_grd                         true
% 11.72/1.99  --splitting_cvd                         false
% 11.72/1.99  --splitting_cvd_svl                     false
% 11.72/1.99  --splitting_nvd                         32
% 11.72/1.99  --sub_typing                            true
% 11.72/1.99  --prep_gs_sim                           false
% 11.72/1.99  --prep_unflatten                        true
% 11.72/1.99  --prep_res_sim                          true
% 11.72/1.99  --prep_upred                            true
% 11.72/1.99  --prep_sem_filter                       exhaustive
% 11.72/1.99  --prep_sem_filter_out                   false
% 11.72/1.99  --pred_elim                             false
% 11.72/1.99  --res_sim_input                         true
% 11.72/1.99  --eq_ax_congr_red                       true
% 11.72/1.99  --pure_diseq_elim                       true
% 11.72/1.99  --brand_transform                       false
% 11.72/1.99  --non_eq_to_eq                          false
% 11.72/1.99  --prep_def_merge                        true
% 11.72/1.99  --prep_def_merge_prop_impl              false
% 11.72/1.99  --prep_def_merge_mbd                    true
% 11.72/1.99  --prep_def_merge_tr_red                 false
% 11.72/1.99  --prep_def_merge_tr_cl                  false
% 11.72/1.99  --smt_preprocessing                     true
% 11.72/1.99  --smt_ac_axioms                         fast
% 11.72/1.99  --preprocessed_out                      false
% 11.72/1.99  --preprocessed_stats                    false
% 11.72/1.99  
% 11.72/1.99  ------ Abstraction refinement Options
% 11.72/1.99  
% 11.72/1.99  --abstr_ref                             []
% 11.72/1.99  --abstr_ref_prep                        false
% 11.72/1.99  --abstr_ref_until_sat                   false
% 11.72/1.99  --abstr_ref_sig_restrict                funpre
% 11.72/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.72/1.99  --abstr_ref_under                       []
% 11.72/1.99  
% 11.72/1.99  ------ SAT Options
% 11.72/1.99  
% 11.72/1.99  --sat_mode                              false
% 11.72/1.99  --sat_fm_restart_options                ""
% 11.72/1.99  --sat_gr_def                            false
% 11.72/1.99  --sat_epr_types                         true
% 11.72/1.99  --sat_non_cyclic_types                  false
% 11.72/1.99  --sat_finite_models                     false
% 11.72/1.99  --sat_fm_lemmas                         false
% 11.72/1.99  --sat_fm_prep                           false
% 11.72/1.99  --sat_fm_uc_incr                        true
% 11.72/1.99  --sat_out_model                         small
% 11.72/1.99  --sat_out_clauses                       false
% 11.72/1.99  
% 11.72/1.99  ------ QBF Options
% 11.72/1.99  
% 11.72/1.99  --qbf_mode                              false
% 11.72/1.99  --qbf_elim_univ                         false
% 11.72/1.99  --qbf_dom_inst                          none
% 11.72/1.99  --qbf_dom_pre_inst                      false
% 11.72/1.99  --qbf_sk_in                             false
% 11.72/1.99  --qbf_pred_elim                         true
% 11.72/1.99  --qbf_split                             512
% 11.72/1.99  
% 11.72/1.99  ------ BMC1 Options
% 11.72/1.99  
% 11.72/1.99  --bmc1_incremental                      false
% 11.72/1.99  --bmc1_axioms                           reachable_all
% 11.72/1.99  --bmc1_min_bound                        0
% 11.72/1.99  --bmc1_max_bound                        -1
% 11.72/1.99  --bmc1_max_bound_default                -1
% 11.72/1.99  --bmc1_symbol_reachability              true
% 11.72/1.99  --bmc1_property_lemmas                  false
% 11.72/1.99  --bmc1_k_induction                      false
% 11.72/1.99  --bmc1_non_equiv_states                 false
% 11.72/1.99  --bmc1_deadlock                         false
% 11.72/1.99  --bmc1_ucm                              false
% 11.72/1.99  --bmc1_add_unsat_core                   none
% 11.72/1.99  --bmc1_unsat_core_children              false
% 11.72/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.72/1.99  --bmc1_out_stat                         full
% 11.72/1.99  --bmc1_ground_init                      false
% 11.72/1.99  --bmc1_pre_inst_next_state              false
% 11.72/1.99  --bmc1_pre_inst_state                   false
% 11.72/1.99  --bmc1_pre_inst_reach_state             false
% 11.72/1.99  --bmc1_out_unsat_core                   false
% 11.72/1.99  --bmc1_aig_witness_out                  false
% 11.72/1.99  --bmc1_verbose                          false
% 11.72/1.99  --bmc1_dump_clauses_tptp                false
% 11.72/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.72/1.99  --bmc1_dump_file                        -
% 11.72/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.72/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.72/1.99  --bmc1_ucm_extend_mode                  1
% 11.72/1.99  --bmc1_ucm_init_mode                    2
% 11.72/1.99  --bmc1_ucm_cone_mode                    none
% 11.72/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.72/1.99  --bmc1_ucm_relax_model                  4
% 11.72/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.72/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.72/1.99  --bmc1_ucm_layered_model                none
% 11.72/1.99  --bmc1_ucm_max_lemma_size               10
% 11.72/1.99  
% 11.72/1.99  ------ AIG Options
% 11.72/1.99  
% 11.72/1.99  --aig_mode                              false
% 11.72/1.99  
% 11.72/1.99  ------ Instantiation Options
% 11.72/1.99  
% 11.72/1.99  --instantiation_flag                    true
% 11.72/1.99  --inst_sos_flag                         false
% 11.72/1.99  --inst_sos_phase                        true
% 11.72/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.72/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.72/1.99  --inst_lit_sel_side                     num_symb
% 11.72/1.99  --inst_solver_per_active                1400
% 11.72/1.99  --inst_solver_calls_frac                1.
% 11.72/1.99  --inst_passive_queue_type               priority_queues
% 11.72/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.72/1.99  --inst_passive_queues_freq              [25;2]
% 11.72/1.99  --inst_dismatching                      true
% 11.72/1.99  --inst_eager_unprocessed_to_passive     true
% 11.72/1.99  --inst_prop_sim_given                   true
% 11.72/1.99  --inst_prop_sim_new                     false
% 11.72/1.99  --inst_subs_new                         false
% 11.72/1.99  --inst_eq_res_simp                      false
% 11.72/1.99  --inst_subs_given                       false
% 11.72/1.99  --inst_orphan_elimination               true
% 11.72/1.99  --inst_learning_loop_flag               true
% 11.72/1.99  --inst_learning_start                   3000
% 11.72/1.99  --inst_learning_factor                  2
% 11.72/1.99  --inst_start_prop_sim_after_learn       3
% 11.72/1.99  --inst_sel_renew                        solver
% 11.72/1.99  --inst_lit_activity_flag                true
% 11.72/1.99  --inst_restr_to_given                   false
% 11.72/1.99  --inst_activity_threshold               500
% 11.72/1.99  --inst_out_proof                        true
% 11.72/1.99  
% 11.72/1.99  ------ Resolution Options
% 11.72/1.99  
% 11.72/1.99  --resolution_flag                       true
% 11.72/1.99  --res_lit_sel                           adaptive
% 11.72/1.99  --res_lit_sel_side                      none
% 11.72/1.99  --res_ordering                          kbo
% 11.72/1.99  --res_to_prop_solver                    active
% 11.72/1.99  --res_prop_simpl_new                    false
% 11.72/1.99  --res_prop_simpl_given                  true
% 11.72/1.99  --res_passive_queue_type                priority_queues
% 11.72/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.72/1.99  --res_passive_queues_freq               [15;5]
% 11.72/1.99  --res_forward_subs                      full
% 11.72/1.99  --res_backward_subs                     full
% 11.72/1.99  --res_forward_subs_resolution           true
% 11.72/1.99  --res_backward_subs_resolution          true
% 11.72/1.99  --res_orphan_elimination                true
% 11.72/1.99  --res_time_limit                        2.
% 11.72/1.99  --res_out_proof                         true
% 11.72/1.99  
% 11.72/1.99  ------ Superposition Options
% 11.72/1.99  
% 11.72/1.99  --superposition_flag                    true
% 11.72/1.99  --sup_passive_queue_type                priority_queues
% 11.72/1.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.72/1.99  --sup_passive_queues_freq               [1;4]
% 11.72/1.99  --demod_completeness_check              fast
% 11.72/1.99  --demod_use_ground                      true
% 11.72/1.99  --sup_to_prop_solver                    passive
% 11.72/1.99  --sup_prop_simpl_new                    true
% 11.72/1.99  --sup_prop_simpl_given                  true
% 11.72/1.99  --sup_fun_splitting                     false
% 11.72/1.99  --sup_smt_interval                      50000
% 11.72/1.99  
% 11.72/1.99  ------ Superposition Simplification Setup
% 11.72/1.99  
% 11.72/1.99  --sup_indices_passive                   []
% 11.72/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.72/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.72/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.72/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.72/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.72/1.99  --sup_full_bw                           [BwDemod]
% 11.72/1.99  --sup_immed_triv                        [TrivRules]
% 11.72/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.72/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.72/1.99  --sup_immed_bw_main                     []
% 11.72/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.72/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.72/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.72/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.72/1.99  
% 11.72/1.99  ------ Combination Options
% 11.72/1.99  
% 11.72/1.99  --comb_res_mult                         3
% 11.72/1.99  --comb_sup_mult                         2
% 11.72/1.99  --comb_inst_mult                        10
% 11.72/1.99  
% 11.72/1.99  ------ Debug Options
% 11.72/1.99  
% 11.72/1.99  --dbg_backtrace                         false
% 11.72/1.99  --dbg_dump_prop_clauses                 false
% 11.72/1.99  --dbg_dump_prop_clauses_file            -
% 11.72/1.99  --dbg_out_stat                          false
% 11.72/1.99  ------ Parsing...
% 11.72/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.72/1.99  
% 11.72/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.72/1.99  
% 11.72/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.72/1.99  
% 11.72/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.72/1.99  ------ Proving...
% 11.72/1.99  ------ Problem Properties 
% 11.72/1.99  
% 11.72/1.99  
% 11.72/1.99  clauses                                 21
% 11.72/1.99  conjectures                             7
% 11.72/1.99  EPR                                     8
% 11.72/1.99  Horn                                    16
% 11.72/1.99  unary                                   4
% 11.72/1.99  binary                                  5
% 11.72/1.99  lits                                    52
% 11.72/1.99  lits eq                                 5
% 11.72/1.99  fd_pure                                 0
% 11.72/1.99  fd_pseudo                               0
% 11.72/1.99  fd_cond                                 0
% 11.72/1.99  fd_pseudo_cond                          3
% 11.72/1.99  AC symbols                              0
% 11.72/1.99  
% 11.72/1.99  ------ Input Options Time Limit: Unbounded
% 11.72/1.99  
% 11.72/1.99  
% 11.72/1.99  ------ 
% 11.72/1.99  Current options:
% 11.72/1.99  ------ 
% 11.72/1.99  
% 11.72/1.99  ------ Input Options
% 11.72/1.99  
% 11.72/1.99  --out_options                           all
% 11.72/1.99  --tptp_safe_out                         true
% 11.72/1.99  --problem_path                          ""
% 11.72/1.99  --include_path                          ""
% 11.72/1.99  --clausifier                            res/vclausify_rel
% 11.72/1.99  --clausifier_options                    --mode clausify
% 11.72/1.99  --stdin                                 false
% 11.72/1.99  --stats_out                             sel
% 11.72/1.99  
% 11.72/1.99  ------ General Options
% 11.72/1.99  
% 11.72/1.99  --fof                                   false
% 11.72/1.99  --time_out_real                         604.99
% 11.72/1.99  --time_out_virtual                      -1.
% 11.72/1.99  --symbol_type_check                     false
% 11.72/1.99  --clausify_out                          false
% 11.72/1.99  --sig_cnt_out                           false
% 11.72/1.99  --trig_cnt_out                          false
% 11.72/1.99  --trig_cnt_out_tolerance                1.
% 11.72/1.99  --trig_cnt_out_sk_spl                   false
% 11.72/1.99  --abstr_cl_out                          false
% 11.72/1.99  
% 11.72/1.99  ------ Global Options
% 11.72/1.99  
% 11.72/1.99  --schedule                              none
% 11.72/1.99  --add_important_lit                     false
% 11.72/1.99  --prop_solver_per_cl                    1000
% 11.72/1.99  --min_unsat_core                        false
% 11.72/1.99  --soft_assumptions                      false
% 11.72/1.99  --soft_lemma_size                       3
% 11.72/1.99  --prop_impl_unit_size                   0
% 11.72/1.99  --prop_impl_unit                        []
% 11.72/1.99  --share_sel_clauses                     true
% 11.72/1.99  --reset_solvers                         false
% 11.72/1.99  --bc_imp_inh                            [conj_cone]
% 11.72/1.99  --conj_cone_tolerance                   3.
% 11.72/1.99  --extra_neg_conj                        none
% 11.72/1.99  --large_theory_mode                     true
% 11.72/1.99  --prolific_symb_bound                   200
% 11.72/1.99  --lt_threshold                          2000
% 11.72/1.99  --clause_weak_htbl                      true
% 11.72/1.99  --gc_record_bc_elim                     false
% 11.72/1.99  
% 11.72/1.99  ------ Preprocessing Options
% 11.72/1.99  
% 11.72/1.99  --preprocessing_flag                    true
% 11.72/1.99  --time_out_prep_mult                    0.1
% 11.72/1.99  --splitting_mode                        input
% 11.72/1.99  --splitting_grd                         true
% 11.72/1.99  --splitting_cvd                         false
% 11.72/1.99  --splitting_cvd_svl                     false
% 11.72/1.99  --splitting_nvd                         32
% 11.72/1.99  --sub_typing                            true
% 11.72/1.99  --prep_gs_sim                           false
% 11.72/1.99  --prep_unflatten                        true
% 11.72/1.99  --prep_res_sim                          true
% 11.72/1.99  --prep_upred                            true
% 11.72/1.99  --prep_sem_filter                       exhaustive
% 11.72/1.99  --prep_sem_filter_out                   false
% 11.72/1.99  --pred_elim                             false
% 11.72/1.99  --res_sim_input                         true
% 11.72/1.99  --eq_ax_congr_red                       true
% 11.72/1.99  --pure_diseq_elim                       true
% 11.72/1.99  --brand_transform                       false
% 11.72/1.99  --non_eq_to_eq                          false
% 11.72/1.99  --prep_def_merge                        true
% 11.72/1.99  --prep_def_merge_prop_impl              false
% 11.72/1.99  --prep_def_merge_mbd                    true
% 11.72/1.99  --prep_def_merge_tr_red                 false
% 11.72/1.99  --prep_def_merge_tr_cl                  false
% 11.72/1.99  --smt_preprocessing                     true
% 11.72/1.99  --smt_ac_axioms                         fast
% 11.72/1.99  --preprocessed_out                      false
% 11.72/1.99  --preprocessed_stats                    false
% 11.72/1.99  
% 11.72/1.99  ------ Abstraction refinement Options
% 11.72/1.99  
% 11.72/1.99  --abstr_ref                             []
% 11.72/1.99  --abstr_ref_prep                        false
% 11.72/1.99  --abstr_ref_until_sat                   false
% 11.72/1.99  --abstr_ref_sig_restrict                funpre
% 11.72/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.72/1.99  --abstr_ref_under                       []
% 11.72/1.99  
% 11.72/1.99  ------ SAT Options
% 11.72/1.99  
% 11.72/1.99  --sat_mode                              false
% 11.72/1.99  --sat_fm_restart_options                ""
% 11.72/1.99  --sat_gr_def                            false
% 11.72/1.99  --sat_epr_types                         true
% 11.72/1.99  --sat_non_cyclic_types                  false
% 11.72/1.99  --sat_finite_models                     false
% 11.72/1.99  --sat_fm_lemmas                         false
% 11.72/1.99  --sat_fm_prep                           false
% 11.72/1.99  --sat_fm_uc_incr                        true
% 11.72/1.99  --sat_out_model                         small
% 11.72/1.99  --sat_out_clauses                       false
% 11.72/1.99  
% 11.72/1.99  ------ QBF Options
% 11.72/1.99  
% 11.72/1.99  --qbf_mode                              false
% 11.72/1.99  --qbf_elim_univ                         false
% 11.72/1.99  --qbf_dom_inst                          none
% 11.72/1.99  --qbf_dom_pre_inst                      false
% 11.72/1.99  --qbf_sk_in                             false
% 11.72/1.99  --qbf_pred_elim                         true
% 11.72/1.99  --qbf_split                             512
% 11.72/1.99  
% 11.72/1.99  ------ BMC1 Options
% 11.72/1.99  
% 11.72/1.99  --bmc1_incremental                      false
% 11.72/1.99  --bmc1_axioms                           reachable_all
% 11.72/1.99  --bmc1_min_bound                        0
% 11.72/1.99  --bmc1_max_bound                        -1
% 11.72/1.99  --bmc1_max_bound_default                -1
% 11.72/1.99  --bmc1_symbol_reachability              true
% 11.72/1.99  --bmc1_property_lemmas                  false
% 11.72/1.99  --bmc1_k_induction                      false
% 11.72/1.99  --bmc1_non_equiv_states                 false
% 11.72/1.99  --bmc1_deadlock                         false
% 11.72/1.99  --bmc1_ucm                              false
% 11.72/1.99  --bmc1_add_unsat_core                   none
% 11.72/1.99  --bmc1_unsat_core_children              false
% 11.72/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.72/1.99  --bmc1_out_stat                         full
% 11.72/1.99  --bmc1_ground_init                      false
% 11.72/1.99  --bmc1_pre_inst_next_state              false
% 11.72/1.99  --bmc1_pre_inst_state                   false
% 11.72/1.99  --bmc1_pre_inst_reach_state             false
% 11.72/1.99  --bmc1_out_unsat_core                   false
% 11.72/1.99  --bmc1_aig_witness_out                  false
% 11.72/1.99  --bmc1_verbose                          false
% 11.72/1.99  --bmc1_dump_clauses_tptp                false
% 11.72/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.72/1.99  --bmc1_dump_file                        -
% 11.72/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.72/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.72/1.99  --bmc1_ucm_extend_mode                  1
% 11.72/1.99  --bmc1_ucm_init_mode                    2
% 11.72/1.99  --bmc1_ucm_cone_mode                    none
% 11.72/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.72/1.99  --bmc1_ucm_relax_model                  4
% 11.72/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.72/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.72/1.99  --bmc1_ucm_layered_model                none
% 11.72/1.99  --bmc1_ucm_max_lemma_size               10
% 11.72/1.99  
% 11.72/1.99  ------ AIG Options
% 11.72/1.99  
% 11.72/1.99  --aig_mode                              false
% 11.72/1.99  
% 11.72/1.99  ------ Instantiation Options
% 11.72/1.99  
% 11.72/1.99  --instantiation_flag                    true
% 11.72/1.99  --inst_sos_flag                         false
% 11.72/1.99  --inst_sos_phase                        true
% 11.72/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.72/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.72/1.99  --inst_lit_sel_side                     num_symb
% 11.72/1.99  --inst_solver_per_active                1400
% 11.72/1.99  --inst_solver_calls_frac                1.
% 11.72/1.99  --inst_passive_queue_type               priority_queues
% 11.72/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.72/1.99  --inst_passive_queues_freq              [25;2]
% 11.72/1.99  --inst_dismatching                      true
% 11.72/1.99  --inst_eager_unprocessed_to_passive     true
% 11.72/1.99  --inst_prop_sim_given                   true
% 11.72/1.99  --inst_prop_sim_new                     false
% 11.72/1.99  --inst_subs_new                         false
% 11.72/1.99  --inst_eq_res_simp                      false
% 11.72/1.99  --inst_subs_given                       false
% 11.72/1.99  --inst_orphan_elimination               true
% 11.72/1.99  --inst_learning_loop_flag               true
% 11.72/1.99  --inst_learning_start                   3000
% 11.72/1.99  --inst_learning_factor                  2
% 11.72/1.99  --inst_start_prop_sim_after_learn       3
% 11.72/1.99  --inst_sel_renew                        solver
% 11.72/1.99  --inst_lit_activity_flag                true
% 11.72/1.99  --inst_restr_to_given                   false
% 11.72/1.99  --inst_activity_threshold               500
% 11.72/1.99  --inst_out_proof                        true
% 11.72/1.99  
% 11.72/1.99  ------ Resolution Options
% 11.72/1.99  
% 11.72/1.99  --resolution_flag                       true
% 11.72/1.99  --res_lit_sel                           adaptive
% 11.72/1.99  --res_lit_sel_side                      none
% 11.72/1.99  --res_ordering                          kbo
% 11.72/1.99  --res_to_prop_solver                    active
% 11.72/1.99  --res_prop_simpl_new                    false
% 11.72/1.99  --res_prop_simpl_given                  true
% 11.72/1.99  --res_passive_queue_type                priority_queues
% 11.72/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.72/1.99  --res_passive_queues_freq               [15;5]
% 11.72/1.99  --res_forward_subs                      full
% 11.72/1.99  --res_backward_subs                     full
% 11.72/1.99  --res_forward_subs_resolution           true
% 11.72/1.99  --res_backward_subs_resolution          true
% 11.72/1.99  --res_orphan_elimination                true
% 11.72/1.99  --res_time_limit                        2.
% 11.72/1.99  --res_out_proof                         true
% 11.72/1.99  
% 11.72/1.99  ------ Superposition Options
% 11.72/1.99  
% 11.72/1.99  --superposition_flag                    true
% 11.72/1.99  --sup_passive_queue_type                priority_queues
% 11.72/1.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.72/1.99  --sup_passive_queues_freq               [1;4]
% 11.72/1.99  --demod_completeness_check              fast
% 11.72/1.99  --demod_use_ground                      true
% 11.72/1.99  --sup_to_prop_solver                    passive
% 11.72/1.99  --sup_prop_simpl_new                    true
% 11.72/1.99  --sup_prop_simpl_given                  true
% 11.72/1.99  --sup_fun_splitting                     false
% 11.72/1.99  --sup_smt_interval                      50000
% 11.72/1.99  
% 11.72/1.99  ------ Superposition Simplification Setup
% 11.72/1.99  
% 11.72/1.99  --sup_indices_passive                   []
% 11.72/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.72/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.72/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.72/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.72/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.72/1.99  --sup_full_bw                           [BwDemod]
% 11.72/1.99  --sup_immed_triv                        [TrivRules]
% 11.72/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.72/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.72/1.99  --sup_immed_bw_main                     []
% 11.72/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.72/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.72/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.72/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.72/1.99  
% 11.72/1.99  ------ Combination Options
% 11.72/1.99  
% 11.72/1.99  --comb_res_mult                         3
% 11.72/1.99  --comb_sup_mult                         2
% 11.72/1.99  --comb_inst_mult                        10
% 11.72/1.99  
% 11.72/1.99  ------ Debug Options
% 11.72/1.99  
% 11.72/1.99  --dbg_backtrace                         false
% 11.72/1.99  --dbg_dump_prop_clauses                 false
% 11.72/1.99  --dbg_dump_prop_clauses_file            -
% 11.72/1.99  --dbg_out_stat                          false
% 11.72/1.99  
% 11.72/1.99  
% 11.72/1.99  
% 11.72/1.99  
% 11.72/1.99  ------ Proving...
% 11.72/1.99  
% 11.72/1.99  
% 11.72/1.99  % SZS status Theorem for theBenchmark.p
% 11.72/1.99  
% 11.72/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.72/1.99  
% 11.72/1.99  fof(f2,axiom,(
% 11.72/1.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 11.72/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f18,plain,(
% 11.72/1.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.72/1.99    inference(nnf_transformation,[],[f2])).
% 11.72/1.99  
% 11.72/1.99  fof(f19,plain,(
% 11.72/1.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.72/1.99    inference(flattening,[],[f18])).
% 11.72/1.99  
% 11.72/1.99  fof(f20,plain,(
% 11.72/1.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.72/1.99    inference(rectify,[],[f19])).
% 11.72/1.99  
% 11.72/1.99  fof(f21,plain,(
% 11.72/1.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 11.72/1.99    introduced(choice_axiom,[])).
% 11.72/1.99  
% 11.72/1.99  fof(f22,plain,(
% 11.72/1.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.72/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).
% 11.72/1.99  
% 11.72/1.99  fof(f35,plain,(
% 11.72/1.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 11.72/1.99    inference(cnf_transformation,[],[f22])).
% 11.72/1.99  
% 11.72/1.99  fof(f5,axiom,(
% 11.72/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 11.72/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f10,plain,(
% 11.72/1.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.72/1.99    inference(ennf_transformation,[],[f5])).
% 11.72/1.99  
% 11.72/1.99  fof(f11,plain,(
% 11.72/1.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.72/1.99    inference(flattening,[],[f10])).
% 11.72/1.99  
% 11.72/1.99  fof(f43,plain,(
% 11.72/1.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.72/1.99    inference(cnf_transformation,[],[f11])).
% 11.72/1.99  
% 11.72/1.99  fof(f6,conjecture,(
% 11.72/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) | r2_hidden(X4,X2)))) => k4_subset_1(X0,X2,X3) = X1))))),
% 11.72/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f7,negated_conjecture,(
% 11.72/1.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) | r2_hidden(X4,X2)))) => k4_subset_1(X0,X2,X3) = X1))))),
% 11.72/1.99    inference(negated_conjecture,[],[f6])).
% 11.72/1.99  
% 11.72/1.99  fof(f12,plain,(
% 11.72/1.99    ? [X0,X1] : (? [X2] : (? [X3] : ((k4_subset_1(X0,X2,X3) != X1 & ! [X4] : ((r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) | r2_hidden(X4,X2))) | ~m1_subset_1(X4,X0))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.72/1.99    inference(ennf_transformation,[],[f7])).
% 11.72/1.99  
% 11.72/1.99  fof(f13,plain,(
% 11.72/1.99    ? [X0,X1] : (? [X2] : (? [X3] : (k4_subset_1(X0,X2,X3) != X1 & ! [X4] : ((r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) | r2_hidden(X4,X2))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.72/1.99    inference(flattening,[],[f12])).
% 11.72/1.99  
% 11.72/1.99  fof(f24,plain,(
% 11.72/1.99    ? [X0,X1] : (? [X2] : (? [X3] : (k4_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & ((r2_hidden(X4,X3) | r2_hidden(X4,X2)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.72/1.99    inference(nnf_transformation,[],[f13])).
% 11.72/1.99  
% 11.72/1.99  fof(f25,plain,(
% 11.72/1.99    ? [X0,X1] : (? [X2] : (? [X3] : (k4_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & (r2_hidden(X4,X3) | r2_hidden(X4,X2) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.72/1.99    inference(flattening,[],[f24])).
% 11.72/1.99  
% 11.72/1.99  fof(f28,plain,(
% 11.72/1.99    ( ! [X2,X0,X1] : (? [X3] : (k4_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & (r2_hidden(X4,X3) | r2_hidden(X4,X2) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (k4_subset_1(X0,X2,sK5) != X1 & ! [X4] : (((r2_hidden(X4,X1) | (~r2_hidden(X4,sK5) & ~r2_hidden(X4,X2))) & (r2_hidden(X4,sK5) | r2_hidden(X4,X2) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(sK5,k1_zfmisc_1(X0)))) )),
% 11.72/1.99    introduced(choice_axiom,[])).
% 11.72/1.99  
% 11.72/1.99  fof(f27,plain,(
% 11.72/1.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (k4_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & (r2_hidden(X4,X3) | r2_hidden(X4,X2) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (? [X3] : (k4_subset_1(X0,sK4,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,sK4))) & (r2_hidden(X4,X3) | r2_hidden(X4,sK4) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(sK4,k1_zfmisc_1(X0)))) )),
% 11.72/1.99    introduced(choice_axiom,[])).
% 11.72/1.99  
% 11.72/1.99  fof(f26,plain,(
% 11.72/1.99    ? [X0,X1] : (? [X2] : (? [X3] : (k4_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & (r2_hidden(X4,X3) | r2_hidden(X4,X2) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (? [X3] : (k4_subset_1(sK2,X2,X3) != sK3 & ! [X4] : (((r2_hidden(X4,sK3) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & (r2_hidden(X4,X3) | r2_hidden(X4,X2) | ~r2_hidden(X4,sK3))) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(sK2))) & m1_subset_1(X2,k1_zfmisc_1(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(sK2)))),
% 11.72/1.99    introduced(choice_axiom,[])).
% 11.72/1.99  
% 11.72/1.99  fof(f29,plain,(
% 11.72/1.99    ((k4_subset_1(sK2,sK4,sK5) != sK3 & ! [X4] : (((r2_hidden(X4,sK3) | (~r2_hidden(X4,sK5) & ~r2_hidden(X4,sK4))) & (r2_hidden(X4,sK5) | r2_hidden(X4,sK4) | ~r2_hidden(X4,sK3))) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 11.72/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f28,f27,f26])).
% 11.72/1.99  
% 11.72/1.99  fof(f50,plain,(
% 11.72/1.99    k4_subset_1(sK2,sK4,sK5) != sK3),
% 11.72/1.99    inference(cnf_transformation,[],[f29])).
% 11.72/1.99  
% 11.72/1.99  fof(f45,plain,(
% 11.72/1.99    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 11.72/1.99    inference(cnf_transformation,[],[f29])).
% 11.72/1.99  
% 11.72/1.99  fof(f46,plain,(
% 11.72/1.99    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 11.72/1.99    inference(cnf_transformation,[],[f29])).
% 11.72/1.99  
% 11.72/1.99  fof(f49,plain,(
% 11.72/1.99    ( ! [X4] : (r2_hidden(X4,sK3) | ~r2_hidden(X4,sK5) | ~m1_subset_1(X4,sK2)) )),
% 11.72/1.99    inference(cnf_transformation,[],[f29])).
% 11.72/1.99  
% 11.72/1.99  fof(f4,axiom,(
% 11.72/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 11.72/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f9,plain,(
% 11.72/1.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.72/1.99    inference(ennf_transformation,[],[f4])).
% 11.72/1.99  
% 11.72/1.99  fof(f42,plain,(
% 11.72/1.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.72/1.99    inference(cnf_transformation,[],[f9])).
% 11.72/1.99  
% 11.72/1.99  fof(f44,plain,(
% 11.72/1.99    m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 11.72/1.99    inference(cnf_transformation,[],[f29])).
% 11.72/1.99  
% 11.72/1.99  fof(f48,plain,(
% 11.72/1.99    ( ! [X4] : (r2_hidden(X4,sK3) | ~r2_hidden(X4,sK4) | ~m1_subset_1(X4,sK2)) )),
% 11.72/1.99    inference(cnf_transformation,[],[f29])).
% 11.72/1.99  
% 11.72/1.99  fof(f3,axiom,(
% 11.72/1.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.72/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f8,plain,(
% 11.72/1.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.72/1.99    inference(ennf_transformation,[],[f3])).
% 11.72/1.99  
% 11.72/1.99  fof(f23,plain,(
% 11.72/1.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.72/1.99    inference(nnf_transformation,[],[f8])).
% 11.72/1.99  
% 11.72/1.99  fof(f39,plain,(
% 11.72/1.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 11.72/1.99    inference(cnf_transformation,[],[f23])).
% 11.72/1.99  
% 11.72/1.99  fof(f1,axiom,(
% 11.72/1.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 11.72/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f14,plain,(
% 11.72/1.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 11.72/1.99    inference(nnf_transformation,[],[f1])).
% 11.72/1.99  
% 11.72/1.99  fof(f15,plain,(
% 11.72/1.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.72/1.99    inference(rectify,[],[f14])).
% 11.72/1.99  
% 11.72/1.99  fof(f16,plain,(
% 11.72/1.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 11.72/1.99    introduced(choice_axiom,[])).
% 11.72/1.99  
% 11.72/1.99  fof(f17,plain,(
% 11.72/1.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.72/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 11.72/1.99  
% 11.72/1.99  fof(f30,plain,(
% 11.72/1.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 11.72/1.99    inference(cnf_transformation,[],[f17])).
% 11.72/1.99  
% 11.72/1.99  fof(f47,plain,(
% 11.72/1.99    ( ! [X4] : (r2_hidden(X4,sK5) | r2_hidden(X4,sK4) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,sK2)) )),
% 11.72/1.99    inference(cnf_transformation,[],[f29])).
% 11.72/1.99  
% 11.72/1.99  fof(f37,plain,(
% 11.72/1.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 11.72/1.99    inference(cnf_transformation,[],[f22])).
% 11.72/1.99  
% 11.72/1.99  fof(f36,plain,(
% 11.72/1.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 11.72/1.99    inference(cnf_transformation,[],[f22])).
% 11.72/1.99  
% 11.72/1.99  cnf(c_4,plain,
% 11.72/1.99      ( r2_hidden(sK1(X0,X1,X2),X1)
% 11.72/1.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 11.72/1.99      | r2_hidden(sK1(X0,X1,X2),X0)
% 11.72/1.99      | k2_xboole_0(X0,X1) = X2 ),
% 11.72/1.99      inference(cnf_transformation,[],[f35]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_187,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_186,plain,( X0 = X0 ),theory(equality) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_1852,plain,
% 11.72/1.99      ( X0 != X1 | X1 = X0 ),
% 11.72/1.99      inference(resolution,[status(thm)],[c_187,c_186]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_2982,plain,
% 11.72/1.99      ( r2_hidden(sK1(X0,X1,X2),X1)
% 11.72/1.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 11.72/1.99      | r2_hidden(sK1(X0,X1,X2),X0)
% 11.72/1.99      | X2 = k2_xboole_0(X0,X1) ),
% 11.72/1.99      inference(resolution,[status(thm)],[c_4,c_1852]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_13,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.72/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.72/1.99      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 11.72/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_1939,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.72/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.72/1.99      | X3 != k2_xboole_0(X0,X2)
% 11.72/1.99      | k4_subset_1(X1,X0,X2) = X3 ),
% 11.72/1.99      inference(resolution,[status(thm)],[c_13,c_187]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_14,negated_conjecture,
% 11.72/1.99      ( k4_subset_1(sK2,sK4,sK5) != sK3 ),
% 11.72/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_6160,plain,
% 11.72/1.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
% 11.72/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 11.72/1.99      | sK3 != k2_xboole_0(sK4,sK5) ),
% 11.72/1.99      inference(resolution,[status(thm)],[c_1939,c_14]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_19,negated_conjecture,
% 11.72/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 11.72/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_18,negated_conjecture,
% 11.72/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 11.72/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_722,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
% 11.72/1.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
% 11.72/1.99      | k4_subset_1(sK2,X0,sK5) = k2_xboole_0(X0,sK5) ),
% 11.72/1.99      inference(instantiation,[status(thm)],[c_13]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_749,plain,
% 11.72/1.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK2))
% 11.72/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 11.72/1.99      | k4_subset_1(sK2,sK4,sK5) = k2_xboole_0(sK4,sK5) ),
% 11.72/1.99      inference(instantiation,[status(thm)],[c_722]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_692,plain,
% 11.72/1.99      ( k4_subset_1(sK2,sK4,sK5) != X0
% 11.72/1.99      | k4_subset_1(sK2,sK4,sK5) = sK3
% 11.72/1.99      | sK3 != X0 ),
% 11.72/1.99      inference(instantiation,[status(thm)],[c_187]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_1053,plain,
% 11.72/1.99      ( k4_subset_1(sK2,sK4,sK5) != k2_xboole_0(X0,X1)
% 11.72/1.99      | k4_subset_1(sK2,sK4,sK5) = sK3
% 11.72/1.99      | sK3 != k2_xboole_0(X0,X1) ),
% 11.72/1.99      inference(instantiation,[status(thm)],[c_692]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_1165,plain,
% 11.72/1.99      ( k4_subset_1(sK2,sK4,sK5) != k2_xboole_0(sK4,sK5)
% 11.72/1.99      | k4_subset_1(sK2,sK4,sK5) = sK3
% 11.72/1.99      | sK3 != k2_xboole_0(sK4,sK5) ),
% 11.72/1.99      inference(instantiation,[status(thm)],[c_1053]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_6661,plain,
% 11.72/1.99      ( sK3 != k2_xboole_0(sK4,sK5) ),
% 11.72/1.99      inference(global_propositional_subsumption,
% 11.72/1.99                [status(thm)],
% 11.72/1.99                [c_6160,c_19,c_18,c_14,c_749,c_1165]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_38883,plain,
% 11.72/1.99      ( r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 11.72/1.99      | r2_hidden(sK1(sK4,sK5,sK3),sK5)
% 11.72/1.99      | r2_hidden(sK1(sK4,sK5,sK3),sK4) ),
% 11.72/1.99      inference(resolution,[status(thm)],[c_2982,c_6661]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_15,negated_conjecture,
% 11.72/1.99      ( ~ m1_subset_1(X0,sK2) | r2_hidden(X0,sK3) | ~ r2_hidden(X0,sK5) ),
% 11.72/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_3526,plain,
% 11.72/1.99      ( ~ m1_subset_1(sK1(sK4,sK5,sK3),sK2)
% 11.72/1.99      | r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 11.72/1.99      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK5) ),
% 11.72/1.99      inference(instantiation,[status(thm)],[c_15]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_495,plain,
% 11.72/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 11.72/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_494,plain,
% 11.72/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 11.72/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_499,plain,
% 11.72/1.99      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 11.72/1.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 11.72/1.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 11.72/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_1244,plain,
% 11.72/1.99      ( k4_subset_1(sK2,sK4,X0) = k2_xboole_0(sK4,X0)
% 11.72/1.99      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top ),
% 11.72/1.99      inference(superposition,[status(thm)],[c_494,c_499]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_4258,plain,
% 11.72/1.99      ( k4_subset_1(sK2,sK4,sK5) = k2_xboole_0(sK4,sK5) ),
% 11.72/1.99      inference(superposition,[status(thm)],[c_495,c_1244]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_4649,plain,
% 11.72/1.99      ( k2_xboole_0(sK4,sK5) != sK3 ),
% 11.72/1.99      inference(demodulation,[status(thm)],[c_4258,c_14]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_12,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.72/1.99      | ~ r2_hidden(X2,X0)
% 11.72/1.99      | r2_hidden(X2,X1) ),
% 11.72/1.99      inference(cnf_transformation,[],[f42]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_1430,plain,
% 11.72/1.99      ( ~ r2_hidden(X0,sK4) | r2_hidden(X0,sK2) ),
% 11.72/1.99      inference(resolution,[status(thm)],[c_12,c_19]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_3008,plain,
% 11.72/1.99      ( r2_hidden(sK1(sK4,X0,X1),X0)
% 11.72/1.99      | r2_hidden(sK1(sK4,X0,X1),X1)
% 11.72/1.99      | r2_hidden(sK1(sK4,X0,X1),sK2)
% 11.72/1.99      | k2_xboole_0(sK4,X0) = X1 ),
% 11.72/1.99      inference(resolution,[status(thm)],[c_4,c_1430]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_20,negated_conjecture,
% 11.72/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
% 11.72/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_1432,plain,
% 11.72/1.99      ( ~ r2_hidden(X0,sK3) | r2_hidden(X0,sK2) ),
% 11.72/1.99      inference(resolution,[status(thm)],[c_12,c_20]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_13784,plain,
% 11.72/1.99      ( r2_hidden(sK1(sK4,X0,sK3),X0)
% 11.72/1.99      | r2_hidden(sK1(sK4,X0,sK3),sK2)
% 11.72/1.99      | k2_xboole_0(sK4,X0) = sK3 ),
% 11.72/1.99      inference(resolution,[status(thm)],[c_3008,c_1432]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_1428,plain,
% 11.72/1.99      ( ~ r2_hidden(X0,sK5) | r2_hidden(X0,sK2) ),
% 11.72/1.99      inference(resolution,[status(thm)],[c_12,c_18]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_14942,plain,
% 11.72/1.99      ( r2_hidden(sK1(sK4,sK5,sK3),sK2) | k2_xboole_0(sK4,sK5) = sK3 ),
% 11.72/1.99      inference(resolution,[status(thm)],[c_13784,c_1428]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_16,negated_conjecture,
% 11.72/1.99      ( ~ m1_subset_1(X0,sK2) | r2_hidden(X0,sK3) | ~ r2_hidden(X0,sK4) ),
% 11.72/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_1490,plain,
% 11.72/1.99      ( ~ m1_subset_1(sK1(sK4,X0,sK3),sK2)
% 11.72/1.99      | r2_hidden(sK1(sK4,X0,sK3),sK3)
% 11.72/1.99      | ~ r2_hidden(sK1(sK4,X0,sK3),sK4) ),
% 11.72/1.99      inference(instantiation,[status(thm)],[c_16]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_29303,plain,
% 11.72/1.99      ( ~ m1_subset_1(sK1(sK4,sK5,sK3),sK2)
% 11.72/1.99      | r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 11.72/1.99      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK4) ),
% 11.72/1.99      inference(instantiation,[status(thm)],[c_1490]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_10,plain,
% 11.72/1.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.72/1.99      inference(cnf_transformation,[],[f39]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_1,plain,
% 11.72/1.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 11.72/1.99      inference(cnf_transformation,[],[f30]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_150,plain,
% 11.72/1.99      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 11.72/1.99      inference(global_propositional_subsumption,
% 11.72/1.99                [status(thm)],
% 11.72/1.99                [c_10,c_1]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_151,plain,
% 11.72/1.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 11.72/1.99      inference(renaming,[status(thm)],[c_150]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_38008,plain,
% 11.72/1.99      ( m1_subset_1(sK1(sK4,sK5,sK3),sK2)
% 11.72/1.99      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK2) ),
% 11.72/1.99      inference(instantiation,[status(thm)],[c_151]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_41110,plain,
% 11.72/1.99      ( r2_hidden(sK1(sK4,sK5,sK3),sK3) ),
% 11.72/1.99      inference(global_propositional_subsumption,
% 11.72/1.99                [status(thm)],
% 11.72/1.99                [c_38883,c_3526,c_4649,c_14942,c_29303,c_38008]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_17,negated_conjecture,
% 11.72/1.99      ( ~ m1_subset_1(X0,sK2)
% 11.72/1.99      | ~ r2_hidden(X0,sK3)
% 11.72/1.99      | r2_hidden(X0,sK5)
% 11.72/1.99      | r2_hidden(X0,sK4) ),
% 11.72/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_872,plain,
% 11.72/1.99      ( ~ r2_hidden(X0,sK3)
% 11.72/1.99      | r2_hidden(X0,sK5)
% 11.72/1.99      | r2_hidden(X0,sK4)
% 11.72/1.99      | ~ r2_hidden(X0,sK2) ),
% 11.72/1.99      inference(resolution,[status(thm)],[c_17,c_151]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_1594,plain,
% 11.72/1.99      ( ~ r2_hidden(X0,sK3) | r2_hidden(X0,sK5) | r2_hidden(X0,sK4) ),
% 11.72/1.99      inference(backward_subsumption_resolution,
% 11.72/1.99                [status(thm)],
% 11.72/1.99                [c_1432,c_872]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_41129,plain,
% 11.72/1.99      ( r2_hidden(sK1(sK4,sK5,sK3),sK5)
% 11.72/1.99      | r2_hidden(sK1(sK4,sK5,sK3),sK4) ),
% 11.72/1.99      inference(resolution,[status(thm)],[c_41110,c_1594]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_2,plain,
% 11.72/1.99      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 11.72/1.99      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 11.72/1.99      | k2_xboole_0(X0,X1) = X2 ),
% 11.72/1.99      inference(cnf_transformation,[],[f37]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_922,plain,
% 11.72/1.99      ( ~ r2_hidden(sK1(X0,X1,sK3),X1)
% 11.72/1.99      | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
% 11.72/1.99      | k2_xboole_0(X0,X1) = sK3 ),
% 11.72/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_5617,plain,
% 11.72/1.99      ( ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 11.72/1.99      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK5)
% 11.72/1.99      | k2_xboole_0(sK4,sK5) = sK3 ),
% 11.72/1.99      inference(instantiation,[status(thm)],[c_922]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_3,plain,
% 11.72/1.99      ( ~ r2_hidden(sK1(X0,X1,X2),X2)
% 11.72/1.99      | ~ r2_hidden(sK1(X0,X1,X2),X0)
% 11.72/1.99      | k2_xboole_0(X0,X1) = X2 ),
% 11.72/1.99      inference(cnf_transformation,[],[f36]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_921,plain,
% 11.72/1.99      ( ~ r2_hidden(sK1(X0,X1,sK3),X0)
% 11.72/1.99      | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
% 11.72/1.99      | k2_xboole_0(X0,X1) = sK3 ),
% 11.72/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_5618,plain,
% 11.72/1.99      ( ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 11.72/1.99      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK4)
% 11.72/1.99      | k2_xboole_0(sK4,sK5) = sK3 ),
% 11.72/1.99      inference(instantiation,[status(thm)],[c_921]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(contradiction,plain,
% 11.72/1.99      ( $false ),
% 11.72/1.99      inference(minisat,
% 11.72/1.99                [status(thm)],
% 11.72/1.99                [c_41129,c_41110,c_5617,c_5618,c_4649]) ).
% 11.72/1.99  
% 11.72/1.99  
% 11.72/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.72/1.99  
% 11.72/1.99  ------                               Statistics
% 11.72/1.99  
% 11.72/1.99  ------ Selected
% 11.72/1.99  
% 11.72/1.99  total_time:                             1.115
% 11.72/1.99  
%------------------------------------------------------------------------------

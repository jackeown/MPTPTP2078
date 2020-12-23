%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0347+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:03 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 420 expanded)
%              Number of clauses        :   56 ( 113 expanded)
%              Number of leaves         :   11 ( 106 expanded)
%              Depth                    :   19
%              Number of atoms          :  454 (3151 expanded)
%              Number of equality atoms :  153 ( 468 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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
    inference(nnf_transformation,[],[f13])).

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

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK1(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK1(X0,X1,X2),X2)
            & r2_hidden(sK1(X0,X1,X2),X1)
            & m1_subset_1(sK1(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f21])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X4] :
      ( r2_hidden(X4,sK4)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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
    inference(flattening,[],[f16])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK5)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    k7_subset_1(sK2,sK4,sK5) != sK3 ),
    inference(cnf_transformation,[],[f28])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f48,plain,(
    ! [X4] :
      ( r2_hidden(X4,sK3)
      | r2_hidden(X4,sK5)
      | ~ r2_hidden(X4,sK4)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_638,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_646,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1153,plain,
    ( k7_subset_1(sK2,sK4,X0) = k4_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_638,c_646])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_647,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1325,plain,
    ( m1_subset_1(k4_xboole_0(sK4,X0),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1153,c_647])).

cnf(c_22,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1798,plain,
    ( m1_subset_1(k4_xboole_0(sK4,X0),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1325,c_22])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK1(X1,X0,X2),X0)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_644,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK1(X1,X0,X2),X0) = iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK1(X1,X0,X2),X1)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_643,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK1(X1,X0,X2),X1) = iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_17,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,sK3)
    | r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_640,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1085,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,X0,X1),sK3) != iProver_top
    | r2_hidden(sK1(sK2,X0,X1),sK4) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_643,c_640])).

cnf(c_1511,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,sK3,X0),sK4) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_644,c_1085])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1895,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,sK3,X0),sK4) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1511,c_21])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_650,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X1,X0,X2),X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_645,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK1(X1,X0,X2),X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2194,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK1(X1,X0,k4_xboole_0(X2,X3)),X2) != iProver_top
    | r2_hidden(sK1(X1,X0,k4_xboole_0(X2,X3)),X3) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_650,c_645])).

cnf(c_10529,plain,
    ( m1_subset_1(k4_xboole_0(sK4,X0),k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,sK3,k4_xboole_0(sK4,X0)),X0) = iProver_top
    | r1_tarski(sK3,k4_xboole_0(sK4,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1895,c_2194])).

cnf(c_10893,plain,
    ( r2_hidden(sK1(sK2,sK3,k4_xboole_0(sK4,X0)),X0) = iProver_top
    | r1_tarski(sK3,k4_xboole_0(sK4,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10529,c_21,c_22,c_1325])).

cnf(c_16,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_641,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1084,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,X0,X1),sK3) != iProver_top
    | r2_hidden(sK1(sK2,X0,X1),sK5) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_643,c_641])).

cnf(c_1512,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,sK3,X0),sK5) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_644,c_1084])).

cnf(c_1888,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,sK3,X0),sK5) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1512,c_21])).

cnf(c_10904,plain,
    ( m1_subset_1(k4_xboole_0(sK4,sK5),k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(sK3,k4_xboole_0(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10893,c_1888])).

cnf(c_14,negated_conjecture,
    ( k7_subset_1(sK2,sK4,sK5) != sK3 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1324,plain,
    ( k4_xboole_0(sK4,sK5) != sK3 ),
    inference(demodulation,[status(thm)],[c_1153,c_14])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_648,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1509,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK1(X1,k4_xboole_0(X2,X3),X0),X2) = iProver_top
    | r1_tarski(k4_xboole_0(X2,X3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_644,c_648])).

cnf(c_15,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | r2_hidden(X0,sK3)
    | r2_hidden(X0,sK5)
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_642,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1083,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,X0,X1),sK3) = iProver_top
    | r2_hidden(sK1(sK2,X0,X1),sK5) = iProver_top
    | r2_hidden(sK1(sK2,X0,X1),sK4) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_643,c_642])).

cnf(c_3896,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(k4_xboole_0(sK4,X1),k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,k4_xboole_0(sK4,X1),X0),sK3) = iProver_top
    | r2_hidden(sK1(sK2,k4_xboole_0(sK4,X1),X0),sK5) = iProver_top
    | r1_tarski(k4_xboole_0(sK4,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_1083])).

cnf(c_4156,plain,
    ( m1_subset_1(k4_xboole_0(sK4,X0),k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,k4_xboole_0(sK4,X0),sK3),sK5) = iProver_top
    | r1_tarski(k4_xboole_0(sK4,X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3896,c_645])).

cnf(c_4502,plain,
    ( r2_hidden(sK1(sK2,k4_xboole_0(sK4,X0),sK3),sK5) = iProver_top
    | r1_tarski(k4_xboole_0(sK4,X0),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4156,c_21,c_22,c_1325])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_649,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1510,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK1(X1,k4_xboole_0(X2,X3),X0),X3) != iProver_top
    | r1_tarski(k4_xboole_0(X2,X3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_644,c_649])).

cnf(c_4728,plain,
    ( m1_subset_1(k4_xboole_0(sK4,sK5),k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(k4_xboole_0(sK4,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4502,c_1510])).

cnf(c_5205,plain,
    ( m1_subset_1(k4_xboole_0(sK4,sK5),k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(k4_xboole_0(sK4,sK5),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4728,c_21])).

cnf(c_5209,plain,
    ( r1_tarski(k4_xboole_0(sK4,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1798,c_5205])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_655,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5259,plain,
    ( k4_xboole_0(sK4,sK5) = sK3
    | r1_tarski(sK3,k4_xboole_0(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5209,c_655])).

cnf(c_11021,plain,
    ( m1_subset_1(k4_xboole_0(sK4,sK5),k1_zfmisc_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10904,c_1324,c_5259])).

cnf(c_11025,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1798,c_11021])).


%------------------------------------------------------------------------------

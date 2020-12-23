%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0346+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:03 EST 2020

% Result     : Theorem 6.89s
% Output     : CNFRefutation 6.89s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 456 expanded)
%              Number of clauses        :   65 ( 128 expanded)
%              Number of leaves         :   12 ( 114 expanded)
%              Depth                    :   20
%              Number of atoms          :  471 (3317 expanded)
%              Number of equality atoms :  168 ( 508 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
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

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK1(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK1(X0,X1,X2),X2)
            & r2_hidden(sK1(X0,X1,X2),X1)
            & m1_subset_1(sK1(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f24])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,conjecture,(
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
                        & r2_hidden(X4,X2) ) ) )
               => k9_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
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
                          & r2_hidden(X4,X2) ) ) )
                 => k9_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k9_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k9_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k9_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k9_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k9_subset_1(X0,X2,X3) != X1
          & ! [X4] :
              ( ( ( r2_hidden(X4,X1)
                  | ~ r2_hidden(X4,X3)
                  | ~ r2_hidden(X4,X2) )
                & ( ( r2_hidden(X4,X3)
                    & r2_hidden(X4,X2) )
                  | ~ r2_hidden(X4,X1) ) )
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( k9_subset_1(X0,X2,sK5) != X1
        & ! [X4] :
            ( ( ( r2_hidden(X4,X1)
                | ~ r2_hidden(X4,sK5)
                | ~ r2_hidden(X4,X2) )
              & ( ( r2_hidden(X4,sK5)
                  & r2_hidden(X4,X2) )
                | ~ r2_hidden(X4,X1) ) )
            | ~ m1_subset_1(X4,X0) )
        & m1_subset_1(sK5,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k9_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ? [X3] :
            ( k9_subset_1(X0,sK4,X3) != X1
            & ! [X4] :
                ( ( ( r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,X3)
                    | ~ r2_hidden(X4,sK4) )
                  & ( ( r2_hidden(X4,X3)
                      & r2_hidden(X4,sK4) )
                    | ~ r2_hidden(X4,X1) ) )
                | ~ m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(X0)) )
        & m1_subset_1(sK4,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k9_subset_1(X0,X2,X3) != X1
                & ! [X4] :
                    ( ( ( r2_hidden(X4,X1)
                        | ~ r2_hidden(X4,X3)
                        | ~ r2_hidden(X4,X2) )
                      & ( ( r2_hidden(X4,X3)
                          & r2_hidden(X4,X2) )
                        | ~ r2_hidden(X4,X1) ) )
                    | ~ m1_subset_1(X4,X0) )
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k9_subset_1(sK2,X2,X3) != sK3
              & ! [X4] :
                  ( ( ( r2_hidden(X4,sK3)
                      | ~ r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,sK3) ) )
                  | ~ m1_subset_1(X4,sK2) )
              & m1_subset_1(X3,k1_zfmisc_1(sK2)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k9_subset_1(sK2,sK4,sK5) != sK3
    & ! [X4] :
        ( ( ( r2_hidden(X4,sK3)
            | ~ r2_hidden(X4,sK5)
            | ~ r2_hidden(X4,sK4) )
          & ( ( r2_hidden(X4,sK5)
              & r2_hidden(X4,sK4) )
            | ~ r2_hidden(X4,sK3) ) )
        | ~ m1_subset_1(X4,sK2) )
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f27,f30,f29,f28])).

fof(f52,plain,(
    ! [X4] :
      ( r2_hidden(X4,sK5)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    ! [X4] :
      ( r2_hidden(X4,sK4)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f53,plain,(
    ! [X4] :
      ( r2_hidden(X4,sK3)
      | ~ r2_hidden(X4,sK5)
      | ~ r2_hidden(X4,sK4)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    k9_subset_1(sK2,sK4,sK5) != sK3 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK1(X1,X2,X0),X2)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_661,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK1(X1,X2,X0),X2) = iProver_top
    | r1_tarski(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK1(X1,X2,X0),X1)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_660,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK1(X1,X2,X0),X1) = iProver_top
    | r1_tarski(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_18,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,sK3)
    | r2_hidden(X0,sK5) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_658,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1197,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,X1,X0),sK3) != iProver_top
    | r2_hidden(sK1(sK2,X1,X0),sK5) = iProver_top
    | r1_tarski(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_660,c_658])).

cnf(c_1772,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,sK3,X0),sK5) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_661,c_1197])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_23,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2712,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,sK3,X0),sK5) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1772,c_23])).

cnf(c_19,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,sK3)
    | r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_657,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1198,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,X1,X0),sK3) != iProver_top
    | r2_hidden(sK1(sK2,X1,X0),sK4) = iProver_top
    | r1_tarski(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_660,c_657])).

cnf(c_1771,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,sK3,X0),sK4) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_661,c_1198])).

cnf(c_2602,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,sK3,X0),sK4) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1771,c_23])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_667,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X1,X2,X0),X0)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_662,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK1(X1,X2,X0),X0) != iProver_top
    | r1_tarski(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3165,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK1(X1,X0,k3_xboole_0(X2,X3)),X3) != iProver_top
    | r2_hidden(sK1(X1,X0,k3_xboole_0(X2,X3)),X2) != iProver_top
    | r1_tarski(X0,k3_xboole_0(X2,X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_667,c_662])).

cnf(c_25541,plain,
    ( m1_subset_1(k3_xboole_0(X0,sK4),k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,sK3,k3_xboole_0(X0,sK4)),X0) != iProver_top
    | r1_tarski(sK3,k3_xboole_0(X0,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2602,c_3165])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_655,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_663,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1521,plain,
    ( k9_subset_1(sK2,X0,sK4) = k3_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_655,c_663])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_664,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2039,plain,
    ( m1_subset_1(k3_xboole_0(X0,sK4),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1521,c_664])).

cnf(c_27315,plain,
    ( r2_hidden(sK1(sK2,sK3,k3_xboole_0(X0,sK4)),X0) != iProver_top
    | r1_tarski(sK3,k3_xboole_0(X0,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25541,c_23,c_24,c_2039])).

cnf(c_27326,plain,
    ( m1_subset_1(k3_xboole_0(sK5,sK4),k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(sK3,k3_xboole_0(sK5,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2712,c_27315])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_656,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1520,plain,
    ( k9_subset_1(sK2,X0,sK5) = k3_xboole_0(X0,sK5) ),
    inference(superposition,[status(thm)],[c_656,c_663])).

cnf(c_2038,plain,
    ( m1_subset_1(k3_xboole_0(X0,sK5),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1520,c_664])).

cnf(c_25,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2461,plain,
    ( m1_subset_1(k3_xboole_0(X0,sK5),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2038,c_25])).

cnf(c_2468,plain,
    ( m1_subset_1(k3_xboole_0(sK5,X0),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2461])).

cnf(c_27462,plain,
    ( r1_tarski(sK3,k3_xboole_0(sK5,sK4)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_27326,c_2468])).

cnf(c_27464,plain,
    ( r1_tarski(sK3,k3_xboole_0(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_27462])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_665,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1770,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK1(X1,k3_xboole_0(X2,X3),X0),X2) = iProver_top
    | r1_tarski(k3_xboole_0(X2,X3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_661,c_665])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_666,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1769,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK1(X1,k3_xboole_0(X2,X3),X0),X3) = iProver_top
    | r1_tarski(k3_xboole_0(X2,X3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_661,c_666])).

cnf(c_17,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_659,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1196,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,X1,X0),sK3) = iProver_top
    | r2_hidden(sK1(sK2,X1,X0),sK5) != iProver_top
    | r2_hidden(sK1(sK2,X1,X0),sK4) != iProver_top
    | r1_tarski(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_660,c_659])).

cnf(c_5190,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(k3_xboole_0(X1,sK5),k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,k3_xboole_0(X1,sK5),X0),sK3) = iProver_top
    | r2_hidden(sK1(sK2,k3_xboole_0(X1,sK5),X0),sK4) != iProver_top
    | r1_tarski(k3_xboole_0(X1,sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1769,c_1196])).

cnf(c_6012,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,k3_xboole_0(X1,sK5),X0),sK3) = iProver_top
    | r2_hidden(sK1(sK2,k3_xboole_0(X1,sK5),X0),sK4) != iProver_top
    | r1_tarski(k3_xboole_0(X1,sK5),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5190,c_2461])).

cnf(c_6587,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(k3_xboole_0(sK4,sK5),k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,k3_xboole_0(sK4,sK5),X0),sK3) = iProver_top
    | r1_tarski(k3_xboole_0(sK4,sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1770,c_6012])).

cnf(c_11229,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,k3_xboole_0(sK4,sK5),X0),sK3) = iProver_top
    | r1_tarski(k3_xboole_0(sK4,sK5),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6587,c_2461])).

cnf(c_11233,plain,
    ( m1_subset_1(k3_xboole_0(sK4,sK5),k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(k3_xboole_0(sK4,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_11229,c_662])).

cnf(c_11252,plain,
    ( m1_subset_1(k3_xboole_0(sK4,sK5),k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(k3_xboole_0(sK4,sK5),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11233,c_23])).

cnf(c_11258,plain,
    ( r1_tarski(k3_xboole_0(sK4,sK5),sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11252,c_2461])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_672,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11260,plain,
    ( k3_xboole_0(sK4,sK5) = sK3
    | r1_tarski(sK3,k3_xboole_0(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11258,c_672])).

cnf(c_16,negated_conjecture,
    ( k9_subset_1(sK2,sK4,sK5) != sK3 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1542,plain,
    ( k3_xboole_0(sK4,sK5) != sK3 ),
    inference(demodulation,[status(thm)],[c_1520,c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27464,c_11260,c_1542])).


%------------------------------------------------------------------------------

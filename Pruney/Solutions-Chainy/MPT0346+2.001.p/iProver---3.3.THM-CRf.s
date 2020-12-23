%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:03 EST 2020

% Result     : Theorem 8.19s
% Output     : CNFRefutation 8.19s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 165 expanded)
%              Number of clauses        :   47 (  48 expanded)
%              Number of leaves         :   11 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  404 (1310 expanded)
%              Number of equality atoms :   48 ( 144 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

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
                        & r2_hidden(X4,X2) ) ) )
               => k9_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                          & r2_hidden(X4,X2) ) ) )
                 => k9_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f27,plain,(
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

fof(f26,plain,(
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

fof(f25,plain,
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

fof(f28,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f27,f26,f25])).

fof(f47,plain,(
    ! [X4] :
      ( r2_hidden(X4,sK5)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X4] :
      ( r2_hidden(X4,sK4)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X4] :
      ( r2_hidden(X4,sK3)
      | ~ r2_hidden(X4,sK5)
      | ~ r2_hidden(X4,sK4)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    k9_subset_1(sK2,sK4,sK5) != sK3 ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3080,plain,
    ( ~ r2_hidden(sK1(X0,X1,sK3),X1)
    | ~ r2_hidden(sK1(X0,X1,sK3),X0)
    | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
    | k3_xboole_0(X0,X1) = sK3 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_6478,plain,
    ( ~ r2_hidden(sK1(sK4,X0,sK3),X0)
    | ~ r2_hidden(sK1(sK4,X0,sK3),sK3)
    | ~ r2_hidden(sK1(sK4,X0,sK3),sK4)
    | k3_xboole_0(sK4,X0) = sK3 ),
    inference(instantiation,[status(thm)],[c_3080])).

cnf(c_25548,plain,
    ( ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK5)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK4)
    | k3_xboole_0(sK4,sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_6478])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1452,plain,
    ( r2_hidden(sK1(X0,X1,sK3),X1)
    | r2_hidden(sK1(X0,X1,sK3),sK3)
    | k3_xboole_0(X0,X1) = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5320,plain,
    ( r2_hidden(sK1(X0,sK5,sK3),sK3)
    | r2_hidden(sK1(X0,sK5,sK3),sK5)
    | k3_xboole_0(X0,sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_1452])).

cnf(c_23787,plain,
    ( r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | r2_hidden(sK1(sK4,sK5,sK3),sK5)
    | k3_xboole_0(sK4,sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_5320])).

cnf(c_16,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,sK3)
    | r2_hidden(X0,sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2287,plain,
    ( ~ m1_subset_1(sK1(X0,X1,sK3),sK2)
    | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
    | r2_hidden(sK1(X0,X1,sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3968,plain,
    ( ~ m1_subset_1(sK1(sK4,X0,sK3),sK2)
    | ~ r2_hidden(sK1(sK4,X0,sK3),sK3)
    | r2_hidden(sK1(sK4,X0,sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_2287])).

cnf(c_23729,plain,
    ( ~ m1_subset_1(sK1(sK4,sK5,sK3),sK2)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | r2_hidden(sK1(sK4,sK5,sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_3968])).

cnf(c_17,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,sK3)
    | r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2286,plain,
    ( ~ m1_subset_1(sK1(X0,X1,sK3),sK2)
    | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
    | r2_hidden(sK1(X0,X1,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3958,plain,
    ( ~ m1_subset_1(sK1(sK4,X0,sK3),sK2)
    | ~ r2_hidden(sK1(sK4,X0,sK3),sK3)
    | r2_hidden(sK1(sK4,X0,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_2286])).

cnf(c_23710,plain,
    ( ~ m1_subset_1(sK1(sK4,sK5,sK3),sK2)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | r2_hidden(sK1(sK4,sK5,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_3958])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1758,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X0,X2,sK3),X0)
    | r2_hidden(sK1(X0,X2,sK3),X1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2426,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK1(sK4,X0,sK3),sK4)
    | r2_hidden(sK1(sK4,X0,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_1758])).

cnf(c_21107,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK4)
    | r2_hidden(sK1(sK4,sK5,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_2426])).

cnf(c_2281,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r2_hidden(sK1(X1,X2,sK3),X0)
    | ~ r2_hidden(sK1(X1,X2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_5953,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r2_hidden(sK1(sK4,X1,sK3),X0)
    | ~ r2_hidden(sK1(sK4,X1,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_2281])).

cnf(c_20955,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r2_hidden(sK1(sK4,sK5,sK3),X0)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_5953])).

cnf(c_20957,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | r2_hidden(sK1(sK4,sK5,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_20955])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1451,plain,
    ( r2_hidden(sK1(X0,X1,sK3),X0)
    | r2_hidden(sK1(X0,X1,sK3),sK3)
    | k3_xboole_0(X0,X1) = sK3 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1761,plain,
    ( r2_hidden(sK1(sK4,X0,sK3),sK3)
    | r2_hidden(sK1(sK4,X0,sK3),sK4)
    | k3_xboole_0(sK4,X0) = sK3 ),
    inference(instantiation,[status(thm)],[c_1451])).

cnf(c_14860,plain,
    ( r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | r2_hidden(sK1(sK4,sK5,sK3),sK4)
    | k3_xboole_0(sK4,sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_1761])).

cnf(c_15,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1762,plain,
    ( ~ m1_subset_1(sK1(sK4,X0,sK3),sK2)
    | r2_hidden(sK1(sK4,X0,sK3),sK3)
    | ~ r2_hidden(sK1(sK4,X0,sK3),sK5)
    | ~ r2_hidden(sK1(sK4,X0,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_9218,plain,
    ( ~ m1_subset_1(sK1(sK4,sK5,sK3),sK2)
    | r2_hidden(sK1(sK4,sK5,sK3),sK3)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK5)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1762])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_117,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_1])).

cnf(c_118,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_117])).

cnf(c_3543,plain,
    ( m1_subset_1(sK1(X0,sK5,sK3),sK2)
    | ~ r2_hidden(sK1(X0,sK5,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_9217,plain,
    ( m1_subset_1(sK1(sK4,sK5,sK3),sK2)
    | ~ r2_hidden(sK1(sK4,sK5,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_3543])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1084,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1088,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1467,plain,
    ( k9_subset_1(sK2,X0,sK5) = k3_xboole_0(X0,sK5) ),
    inference(superposition,[status(thm)],[c_1084,c_1088])).

cnf(c_14,negated_conjecture,
    ( k9_subset_1(sK2,sK4,sK5) != sK3 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1673,plain,
    ( k3_xboole_0(sK4,sK5) != sK3 ),
    inference(demodulation,[status(thm)],[c_1467,c_14])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25548,c_23787,c_23729,c_23710,c_21107,c_20957,c_14860,c_9218,c_9217,c_1673,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n020.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:12:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 8.19/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.19/1.51  
% 8.19/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.19/1.51  
% 8.19/1.51  ------  iProver source info
% 8.19/1.51  
% 8.19/1.51  git: date: 2020-06-30 10:37:57 +0100
% 8.19/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.19/1.51  git: non_committed_changes: false
% 8.19/1.51  git: last_make_outside_of_git: false
% 8.19/1.51  
% 8.19/1.51  ------ 
% 8.19/1.51  ------ Parsing...
% 8.19/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.19/1.51  
% 8.19/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 8.19/1.51  
% 8.19/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.19/1.51  
% 8.19/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.19/1.51  ------ Proving...
% 8.19/1.51  ------ Problem Properties 
% 8.19/1.51  
% 8.19/1.51  
% 8.19/1.51  clauses                                 21
% 8.19/1.51  conjectures                             7
% 8.19/1.51  EPR                                     8
% 8.19/1.51  Horn                                    17
% 8.19/1.51  unary                                   4
% 8.19/1.51  binary                                  6
% 8.19/1.51  lits                                    51
% 8.19/1.51  lits eq                                 5
% 8.19/1.51  fd_pure                                 0
% 8.19/1.51  fd_pseudo                               0
% 8.19/1.51  fd_cond                                 0
% 8.19/1.51  fd_pseudo_cond                          3
% 8.19/1.51  AC symbols                              0
% 8.19/1.51  
% 8.19/1.51  ------ Input Options Time Limit: Unbounded
% 8.19/1.51  
% 8.19/1.51  
% 8.19/1.51  ------ 
% 8.19/1.51  Current options:
% 8.19/1.51  ------ 
% 8.19/1.51  
% 8.19/1.51  
% 8.19/1.51  
% 8.19/1.51  
% 8.19/1.51  ------ Proving...
% 8.19/1.51  
% 8.19/1.51  
% 8.19/1.51  % SZS status Theorem for theBenchmark.p
% 8.19/1.51  
% 8.19/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 8.19/1.51  
% 8.19/1.51  fof(f2,axiom,(
% 8.19/1.51    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 8.19/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.19/1.51  
% 8.19/1.51  fof(f17,plain,(
% 8.19/1.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 8.19/1.51    inference(nnf_transformation,[],[f2])).
% 8.19/1.51  
% 8.19/1.51  fof(f18,plain,(
% 8.19/1.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 8.19/1.51    inference(flattening,[],[f17])).
% 8.19/1.51  
% 8.19/1.51  fof(f19,plain,(
% 8.19/1.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 8.19/1.51    inference(rectify,[],[f18])).
% 8.19/1.51  
% 8.19/1.51  fof(f20,plain,(
% 8.19/1.51    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 8.19/1.51    introduced(choice_axiom,[])).
% 8.19/1.51  
% 8.19/1.51  fof(f21,plain,(
% 8.19/1.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 8.19/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 8.19/1.51  
% 8.19/1.51  fof(f36,plain,(
% 8.19/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 8.19/1.51    inference(cnf_transformation,[],[f21])).
% 8.19/1.51  
% 8.19/1.51  fof(f35,plain,(
% 8.19/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 8.19/1.51    inference(cnf_transformation,[],[f21])).
% 8.19/1.51  
% 8.19/1.51  fof(f6,conjecture,(
% 8.19/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) & r2_hidden(X4,X2)))) => k9_subset_1(X0,X2,X3) = X1))))),
% 8.19/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.19/1.51  
% 8.19/1.51  fof(f7,negated_conjecture,(
% 8.19/1.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) & r2_hidden(X4,X2)))) => k9_subset_1(X0,X2,X3) = X1))))),
% 8.19/1.51    inference(negated_conjecture,[],[f6])).
% 8.19/1.51  
% 8.19/1.51  fof(f11,plain,(
% 8.19/1.51    ? [X0,X1] : (? [X2] : (? [X3] : ((k9_subset_1(X0,X2,X3) != X1 & ! [X4] : ((r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) & r2_hidden(X4,X2))) | ~m1_subset_1(X4,X0))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.19/1.51    inference(ennf_transformation,[],[f7])).
% 8.19/1.51  
% 8.19/1.51  fof(f12,plain,(
% 8.19/1.51    ? [X0,X1] : (? [X2] : (? [X3] : (k9_subset_1(X0,X2,X3) != X1 & ! [X4] : ((r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) & r2_hidden(X4,X2))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.19/1.51    inference(flattening,[],[f11])).
% 8.19/1.51  
% 8.19/1.51  fof(f23,plain,(
% 8.19/1.51    ? [X0,X1] : (? [X2] : (? [X3] : (k9_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | (~r2_hidden(X4,X3) | ~r2_hidden(X4,X2))) & ((r2_hidden(X4,X3) & r2_hidden(X4,X2)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.19/1.51    inference(nnf_transformation,[],[f12])).
% 8.19/1.51  
% 8.19/1.51  fof(f24,plain,(
% 8.19/1.51    ? [X0,X1] : (? [X2] : (? [X3] : (k9_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | ~r2_hidden(X4,X3) | ~r2_hidden(X4,X2)) & ((r2_hidden(X4,X3) & r2_hidden(X4,X2)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.19/1.51    inference(flattening,[],[f23])).
% 8.19/1.51  
% 8.19/1.51  fof(f27,plain,(
% 8.19/1.51    ( ! [X2,X0,X1] : (? [X3] : (k9_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | ~r2_hidden(X4,X3) | ~r2_hidden(X4,X2)) & ((r2_hidden(X4,X3) & r2_hidden(X4,X2)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (k9_subset_1(X0,X2,sK5) != X1 & ! [X4] : (((r2_hidden(X4,X1) | ~r2_hidden(X4,sK5) | ~r2_hidden(X4,X2)) & ((r2_hidden(X4,sK5) & r2_hidden(X4,X2)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(sK5,k1_zfmisc_1(X0)))) )),
% 8.19/1.51    introduced(choice_axiom,[])).
% 8.19/1.51  
% 8.19/1.51  fof(f26,plain,(
% 8.19/1.51    ( ! [X0,X1] : (? [X2] : (? [X3] : (k9_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | ~r2_hidden(X4,X3) | ~r2_hidden(X4,X2)) & ((r2_hidden(X4,X3) & r2_hidden(X4,X2)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (? [X3] : (k9_subset_1(X0,sK4,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | ~r2_hidden(X4,X3) | ~r2_hidden(X4,sK4)) & ((r2_hidden(X4,X3) & r2_hidden(X4,sK4)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(sK4,k1_zfmisc_1(X0)))) )),
% 8.19/1.51    introduced(choice_axiom,[])).
% 8.19/1.51  
% 8.19/1.51  fof(f25,plain,(
% 8.19/1.51    ? [X0,X1] : (? [X2] : (? [X3] : (k9_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | ~r2_hidden(X4,X3) | ~r2_hidden(X4,X2)) & ((r2_hidden(X4,X3) & r2_hidden(X4,X2)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (? [X3] : (k9_subset_1(sK2,X2,X3) != sK3 & ! [X4] : (((r2_hidden(X4,sK3) | ~r2_hidden(X4,X3) | ~r2_hidden(X4,X2)) & ((r2_hidden(X4,X3) & r2_hidden(X4,X2)) | ~r2_hidden(X4,sK3))) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(sK2))) & m1_subset_1(X2,k1_zfmisc_1(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(sK2)))),
% 8.19/1.51    introduced(choice_axiom,[])).
% 8.19/1.51  
% 8.19/1.51  fof(f28,plain,(
% 8.19/1.51    ((k9_subset_1(sK2,sK4,sK5) != sK3 & ! [X4] : (((r2_hidden(X4,sK3) | ~r2_hidden(X4,sK5) | ~r2_hidden(X4,sK4)) & ((r2_hidden(X4,sK5) & r2_hidden(X4,sK4)) | ~r2_hidden(X4,sK3))) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 8.19/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f27,f26,f25])).
% 8.19/1.51  
% 8.19/1.51  fof(f47,plain,(
% 8.19/1.51    ( ! [X4] : (r2_hidden(X4,sK5) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,sK2)) )),
% 8.19/1.51    inference(cnf_transformation,[],[f28])).
% 8.19/1.51  
% 8.19/1.51  fof(f46,plain,(
% 8.19/1.51    ( ! [X4] : (r2_hidden(X4,sK4) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,sK2)) )),
% 8.19/1.51    inference(cnf_transformation,[],[f28])).
% 8.19/1.51  
% 8.19/1.51  fof(f4,axiom,(
% 8.19/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 8.19/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.19/1.51  
% 8.19/1.51  fof(f9,plain,(
% 8.19/1.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.19/1.51    inference(ennf_transformation,[],[f4])).
% 8.19/1.51  
% 8.19/1.51  fof(f41,plain,(
% 8.19/1.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.19/1.51    inference(cnf_transformation,[],[f9])).
% 8.19/1.51  
% 8.19/1.51  fof(f34,plain,(
% 8.19/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 8.19/1.51    inference(cnf_transformation,[],[f21])).
% 8.19/1.51  
% 8.19/1.51  fof(f48,plain,(
% 8.19/1.51    ( ! [X4] : (r2_hidden(X4,sK3) | ~r2_hidden(X4,sK5) | ~r2_hidden(X4,sK4) | ~m1_subset_1(X4,sK2)) )),
% 8.19/1.51    inference(cnf_transformation,[],[f28])).
% 8.19/1.51  
% 8.19/1.51  fof(f3,axiom,(
% 8.19/1.51    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 8.19/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.19/1.51  
% 8.19/1.51  fof(f8,plain,(
% 8.19/1.51    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 8.19/1.51    inference(ennf_transformation,[],[f3])).
% 8.19/1.51  
% 8.19/1.51  fof(f22,plain,(
% 8.19/1.51    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 8.19/1.51    inference(nnf_transformation,[],[f8])).
% 8.19/1.51  
% 8.19/1.51  fof(f38,plain,(
% 8.19/1.51    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 8.19/1.51    inference(cnf_transformation,[],[f22])).
% 8.19/1.51  
% 8.19/1.51  fof(f1,axiom,(
% 8.19/1.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 8.19/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.19/1.51  
% 8.19/1.51  fof(f13,plain,(
% 8.19/1.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 8.19/1.51    inference(nnf_transformation,[],[f1])).
% 8.19/1.51  
% 8.19/1.51  fof(f14,plain,(
% 8.19/1.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 8.19/1.51    inference(rectify,[],[f13])).
% 8.19/1.51  
% 8.19/1.51  fof(f15,plain,(
% 8.19/1.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 8.19/1.51    introduced(choice_axiom,[])).
% 8.19/1.51  
% 8.19/1.51  fof(f16,plain,(
% 8.19/1.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 8.19/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 8.19/1.51  
% 8.19/1.51  fof(f29,plain,(
% 8.19/1.51    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 8.19/1.51    inference(cnf_transformation,[],[f16])).
% 8.19/1.51  
% 8.19/1.51  fof(f45,plain,(
% 8.19/1.51    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 8.19/1.51    inference(cnf_transformation,[],[f28])).
% 8.19/1.51  
% 8.19/1.51  fof(f5,axiom,(
% 8.19/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 8.19/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.19/1.51  
% 8.19/1.51  fof(f10,plain,(
% 8.19/1.51    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 8.19/1.51    inference(ennf_transformation,[],[f5])).
% 8.19/1.51  
% 8.19/1.51  fof(f42,plain,(
% 8.19/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 8.19/1.51    inference(cnf_transformation,[],[f10])).
% 8.19/1.51  
% 8.19/1.51  fof(f49,plain,(
% 8.19/1.51    k9_subset_1(sK2,sK4,sK5) != sK3),
% 8.19/1.51    inference(cnf_transformation,[],[f28])).
% 8.19/1.51  
% 8.19/1.51  fof(f44,plain,(
% 8.19/1.51    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 8.19/1.51    inference(cnf_transformation,[],[f28])).
% 8.19/1.51  
% 8.19/1.51  fof(f43,plain,(
% 8.19/1.51    m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 8.19/1.51    inference(cnf_transformation,[],[f28])).
% 8.19/1.51  
% 8.19/1.51  cnf(c_2,plain,
% 8.19/1.51      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 8.19/1.51      | ~ r2_hidden(sK1(X0,X1,X2),X0)
% 8.19/1.51      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 8.19/1.51      | k3_xboole_0(X0,X1) = X2 ),
% 8.19/1.51      inference(cnf_transformation,[],[f36]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_3080,plain,
% 8.19/1.51      ( ~ r2_hidden(sK1(X0,X1,sK3),X1)
% 8.19/1.51      | ~ r2_hidden(sK1(X0,X1,sK3),X0)
% 8.19/1.51      | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
% 8.19/1.51      | k3_xboole_0(X0,X1) = sK3 ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_2]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_6478,plain,
% 8.19/1.51      ( ~ r2_hidden(sK1(sK4,X0,sK3),X0)
% 8.19/1.51      | ~ r2_hidden(sK1(sK4,X0,sK3),sK3)
% 8.19/1.51      | ~ r2_hidden(sK1(sK4,X0,sK3),sK4)
% 8.19/1.51      | k3_xboole_0(sK4,X0) = sK3 ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_3080]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_25548,plain,
% 8.19/1.51      ( ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 8.19/1.51      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK5)
% 8.19/1.51      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK4)
% 8.19/1.51      | k3_xboole_0(sK4,sK5) = sK3 ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_6478]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_3,plain,
% 8.19/1.51      ( r2_hidden(sK1(X0,X1,X2),X1)
% 8.19/1.51      | r2_hidden(sK1(X0,X1,X2),X2)
% 8.19/1.51      | k3_xboole_0(X0,X1) = X2 ),
% 8.19/1.51      inference(cnf_transformation,[],[f35]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_1452,plain,
% 8.19/1.51      ( r2_hidden(sK1(X0,X1,sK3),X1)
% 8.19/1.51      | r2_hidden(sK1(X0,X1,sK3),sK3)
% 8.19/1.51      | k3_xboole_0(X0,X1) = sK3 ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_5320,plain,
% 8.19/1.51      ( r2_hidden(sK1(X0,sK5,sK3),sK3)
% 8.19/1.51      | r2_hidden(sK1(X0,sK5,sK3),sK5)
% 8.19/1.51      | k3_xboole_0(X0,sK5) = sK3 ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_1452]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_23787,plain,
% 8.19/1.51      ( r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 8.19/1.51      | r2_hidden(sK1(sK4,sK5,sK3),sK5)
% 8.19/1.51      | k3_xboole_0(sK4,sK5) = sK3 ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_5320]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_16,negated_conjecture,
% 8.19/1.51      ( ~ m1_subset_1(X0,sK2) | ~ r2_hidden(X0,sK3) | r2_hidden(X0,sK5) ),
% 8.19/1.51      inference(cnf_transformation,[],[f47]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_2287,plain,
% 8.19/1.51      ( ~ m1_subset_1(sK1(X0,X1,sK3),sK2)
% 8.19/1.51      | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
% 8.19/1.51      | r2_hidden(sK1(X0,X1,sK3),sK5) ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_16]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_3968,plain,
% 8.19/1.51      ( ~ m1_subset_1(sK1(sK4,X0,sK3),sK2)
% 8.19/1.51      | ~ r2_hidden(sK1(sK4,X0,sK3),sK3)
% 8.19/1.51      | r2_hidden(sK1(sK4,X0,sK3),sK5) ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_2287]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_23729,plain,
% 8.19/1.51      ( ~ m1_subset_1(sK1(sK4,sK5,sK3),sK2)
% 8.19/1.51      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 8.19/1.51      | r2_hidden(sK1(sK4,sK5,sK3),sK5) ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_3968]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_17,negated_conjecture,
% 8.19/1.51      ( ~ m1_subset_1(X0,sK2) | ~ r2_hidden(X0,sK3) | r2_hidden(X0,sK4) ),
% 8.19/1.51      inference(cnf_transformation,[],[f46]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_2286,plain,
% 8.19/1.51      ( ~ m1_subset_1(sK1(X0,X1,sK3),sK2)
% 8.19/1.51      | ~ r2_hidden(sK1(X0,X1,sK3),sK3)
% 8.19/1.51      | r2_hidden(sK1(X0,X1,sK3),sK4) ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_17]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_3958,plain,
% 8.19/1.51      ( ~ m1_subset_1(sK1(sK4,X0,sK3),sK2)
% 8.19/1.51      | ~ r2_hidden(sK1(sK4,X0,sK3),sK3)
% 8.19/1.51      | r2_hidden(sK1(sK4,X0,sK3),sK4) ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_2286]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_23710,plain,
% 8.19/1.51      ( ~ m1_subset_1(sK1(sK4,sK5,sK3),sK2)
% 8.19/1.51      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 8.19/1.51      | r2_hidden(sK1(sK4,sK5,sK3),sK4) ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_3958]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_12,plain,
% 8.19/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.19/1.51      | ~ r2_hidden(X2,X0)
% 8.19/1.51      | r2_hidden(X2,X1) ),
% 8.19/1.51      inference(cnf_transformation,[],[f41]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_1758,plain,
% 8.19/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.19/1.51      | ~ r2_hidden(sK1(X0,X2,sK3),X0)
% 8.19/1.51      | r2_hidden(sK1(X0,X2,sK3),X1) ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_12]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_2426,plain,
% 8.19/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 8.19/1.51      | ~ r2_hidden(sK1(sK4,X0,sK3),sK4)
% 8.19/1.51      | r2_hidden(sK1(sK4,X0,sK3),sK2) ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_1758]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_21107,plain,
% 8.19/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 8.19/1.51      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK4)
% 8.19/1.51      | r2_hidden(sK1(sK4,sK5,sK3),sK2) ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_2426]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_2281,plain,
% 8.19/1.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 8.19/1.51      | r2_hidden(sK1(X1,X2,sK3),X0)
% 8.19/1.51      | ~ r2_hidden(sK1(X1,X2,sK3),sK3) ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_12]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_5953,plain,
% 8.19/1.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 8.19/1.51      | r2_hidden(sK1(sK4,X1,sK3),X0)
% 8.19/1.51      | ~ r2_hidden(sK1(sK4,X1,sK3),sK3) ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_2281]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_20955,plain,
% 8.19/1.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 8.19/1.51      | r2_hidden(sK1(sK4,sK5,sK3),X0)
% 8.19/1.51      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK3) ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_5953]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_20957,plain,
% 8.19/1.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
% 8.19/1.51      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 8.19/1.51      | r2_hidden(sK1(sK4,sK5,sK3),sK2) ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_20955]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_4,plain,
% 8.19/1.51      ( r2_hidden(sK1(X0,X1,X2),X0)
% 8.19/1.51      | r2_hidden(sK1(X0,X1,X2),X2)
% 8.19/1.51      | k3_xboole_0(X0,X1) = X2 ),
% 8.19/1.51      inference(cnf_transformation,[],[f34]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_1451,plain,
% 8.19/1.51      ( r2_hidden(sK1(X0,X1,sK3),X0)
% 8.19/1.51      | r2_hidden(sK1(X0,X1,sK3),sK3)
% 8.19/1.51      | k3_xboole_0(X0,X1) = sK3 ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_1761,plain,
% 8.19/1.51      ( r2_hidden(sK1(sK4,X0,sK3),sK3)
% 8.19/1.51      | r2_hidden(sK1(sK4,X0,sK3),sK4)
% 8.19/1.51      | k3_xboole_0(sK4,X0) = sK3 ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_1451]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_14860,plain,
% 8.19/1.51      ( r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 8.19/1.51      | r2_hidden(sK1(sK4,sK5,sK3),sK4)
% 8.19/1.51      | k3_xboole_0(sK4,sK5) = sK3 ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_1761]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_15,negated_conjecture,
% 8.19/1.51      ( ~ m1_subset_1(X0,sK2)
% 8.19/1.51      | r2_hidden(X0,sK3)
% 8.19/1.51      | ~ r2_hidden(X0,sK5)
% 8.19/1.51      | ~ r2_hidden(X0,sK4) ),
% 8.19/1.51      inference(cnf_transformation,[],[f48]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_1762,plain,
% 8.19/1.51      ( ~ m1_subset_1(sK1(sK4,X0,sK3),sK2)
% 8.19/1.51      | r2_hidden(sK1(sK4,X0,sK3),sK3)
% 8.19/1.51      | ~ r2_hidden(sK1(sK4,X0,sK3),sK5)
% 8.19/1.51      | ~ r2_hidden(sK1(sK4,X0,sK3),sK4) ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_9218,plain,
% 8.19/1.51      ( ~ m1_subset_1(sK1(sK4,sK5,sK3),sK2)
% 8.19/1.51      | r2_hidden(sK1(sK4,sK5,sK3),sK3)
% 8.19/1.51      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK5)
% 8.19/1.51      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK4) ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_1762]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_10,plain,
% 8.19/1.51      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 8.19/1.51      inference(cnf_transformation,[],[f38]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_1,plain,
% 8.19/1.51      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 8.19/1.51      inference(cnf_transformation,[],[f29]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_117,plain,
% 8.19/1.51      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 8.19/1.51      inference(global_propositional_subsumption,
% 8.19/1.51                [status(thm)],
% 8.19/1.51                [c_10,c_1]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_118,plain,
% 8.19/1.51      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 8.19/1.51      inference(renaming,[status(thm)],[c_117]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_3543,plain,
% 8.19/1.51      ( m1_subset_1(sK1(X0,sK5,sK3),sK2)
% 8.19/1.51      | ~ r2_hidden(sK1(X0,sK5,sK3),sK2) ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_118]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_9217,plain,
% 8.19/1.51      ( m1_subset_1(sK1(sK4,sK5,sK3),sK2)
% 8.19/1.51      | ~ r2_hidden(sK1(sK4,sK5,sK3),sK2) ),
% 8.19/1.51      inference(instantiation,[status(thm)],[c_3543]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_18,negated_conjecture,
% 8.19/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 8.19/1.51      inference(cnf_transformation,[],[f45]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_1084,plain,
% 8.19/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 8.19/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_13,plain,
% 8.19/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.19/1.51      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 8.19/1.51      inference(cnf_transformation,[],[f42]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_1088,plain,
% 8.19/1.51      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 8.19/1.51      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 8.19/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_1467,plain,
% 8.19/1.51      ( k9_subset_1(sK2,X0,sK5) = k3_xboole_0(X0,sK5) ),
% 8.19/1.51      inference(superposition,[status(thm)],[c_1084,c_1088]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_14,negated_conjecture,
% 8.19/1.51      ( k9_subset_1(sK2,sK4,sK5) != sK3 ),
% 8.19/1.51      inference(cnf_transformation,[],[f49]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_1673,plain,
% 8.19/1.51      ( k3_xboole_0(sK4,sK5) != sK3 ),
% 8.19/1.51      inference(demodulation,[status(thm)],[c_1467,c_14]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_19,negated_conjecture,
% 8.19/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 8.19/1.51      inference(cnf_transformation,[],[f44]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(c_20,negated_conjecture,
% 8.19/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
% 8.19/1.51      inference(cnf_transformation,[],[f43]) ).
% 8.19/1.51  
% 8.19/1.51  cnf(contradiction,plain,
% 8.19/1.51      ( $false ),
% 8.19/1.51      inference(minisat,
% 8.19/1.51                [status(thm)],
% 8.19/1.51                [c_25548,c_23787,c_23729,c_23710,c_21107,c_20957,c_14860,
% 8.19/1.51                 c_9218,c_9217,c_1673,c_19,c_20]) ).
% 8.19/1.51  
% 8.19/1.51  
% 8.19/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 8.19/1.51  
% 8.19/1.51  ------                               Statistics
% 8.19/1.51  
% 8.19/1.51  ------ Selected
% 8.19/1.51  
% 8.19/1.51  total_time:                             1.01
% 8.19/1.51  
%------------------------------------------------------------------------------

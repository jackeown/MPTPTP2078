%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0836+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:12 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 289 expanded)
%              Number of clauses        :   58 (  80 expanded)
%              Number of leaves         :   18 (  89 expanded)
%              Depth                    :   18
%              Number of atoms          :  383 (1818 expanded)
%              Number of equality atoms :   77 ( 126 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f19])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23,f22,f21])).

fof(f38,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                    <=> ? [X4] :
                          ( r2_hidden(k4_tarski(X3,X4),X2)
                          & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <~> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & ( ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) )
                    | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & ( ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) )
                    | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X3,X5),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(rectify,[],[f30])).

fof(f36,plain,(
    ! [X2,X3,X1] :
      ( ? [X5] :
          ( r2_hidden(k4_tarski(X3,X5),X2)
          & m1_subset_1(X5,X1) )
     => ( r2_hidden(k4_tarski(X3,sK8),X2)
        & m1_subset_1(sK8,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X3,X5),X2)
                & m1_subset_1(X5,X1) )
            | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
          & m1_subset_1(X3,X0) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(k4_tarski(sK7,X4),X2)
              | ~ m1_subset_1(X4,X1) )
          | ~ r2_hidden(sK7,k1_relset_1(X0,X1,X2)) )
        & ( ? [X5] :
              ( r2_hidden(k4_tarski(sK7,X5),X2)
              & m1_subset_1(X5,X1) )
          | r2_hidden(sK7,k1_relset_1(X0,X1,X2)) )
        & m1_subset_1(sK7,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ m1_subset_1(X4,X1) )
                | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
              & ( ? [X5] :
                    ( r2_hidden(k4_tarski(X3,X5),X2)
                    & m1_subset_1(X5,X1) )
                | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),sK6)
                  | ~ m1_subset_1(X4,X1) )
              | ~ r2_hidden(X3,k1_relset_1(X0,X1,sK6)) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X3,X5),sK6)
                  & m1_subset_1(X5,X1) )
              | r2_hidden(X3,k1_relset_1(X0,X1,sK6)) )
            & m1_subset_1(X3,X0) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X3,X5),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                      | ~ m1_subset_1(X4,sK5) )
                  | ~ r2_hidden(X3,k1_relset_1(X0,sK5,X2)) )
                & ( ? [X5] :
                      ( r2_hidden(k4_tarski(X3,X5),X2)
                      & m1_subset_1(X5,sK5) )
                  | r2_hidden(X3,k1_relset_1(X0,sK5,X2)) )
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK5))) )
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                          | ~ m1_subset_1(X4,X1) )
                      | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                    & ( ? [X5] :
                          ( r2_hidden(k4_tarski(X3,X5),X2)
                          & m1_subset_1(X5,X1) )
                      | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                    & m1_subset_1(X3,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(sK4,X1,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X3,X5),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k1_relset_1(sK4,X1,X2)) )
                  & m1_subset_1(X3,sK4) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(sK7,X4),sK6)
          | ~ m1_subset_1(X4,sK5) )
      | ~ r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) )
    & ( ( r2_hidden(k4_tarski(sK7,sK8),sK6)
        & m1_subset_1(sK8,sK5) )
      | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) )
    & m1_subset_1(sK7,sK4)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & ~ v1_xboole_0(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f31,f36,f35,f34,f33,f32])).

fof(f53,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f52,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    m1_subset_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f2,f25])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f27])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(sK7,X4),sK6)
      | ~ m1_subset_1(X4,sK5)
      | ~ r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),sK6)
    | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f37])).

fof(f39,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f39])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_622,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_608,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_614,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1773,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_608,c_614])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_615,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2074,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1773,c_615])).

cnf(c_19,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,plain,
    ( m1_subset_1(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4,plain,
    ( m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_49,plain,
    ( m1_subset_1(sK3(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_51,plain,
    ( m1_subset_1(sK3(sK5),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0,sK5)
    | r2_hidden(X0,sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_719,plain,
    ( ~ m1_subset_1(sK3(sK5),sK5)
    | r2_hidden(sK3(sK5),sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_720,plain,
    ( m1_subset_1(sK3(sK5),sK5) != iProver_top
    | r2_hidden(sK3(sK5),sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_664,plain,
    ( ~ m1_subset_1(X0,sK4)
    | r2_hidden(X0,sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_725,plain,
    ( ~ m1_subset_1(sK7,sK4)
    | r2_hidden(sK7,sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_664])).

cnf(c_726,plain,
    ( m1_subset_1(sK7,sK4) != iProver_top
    | r2_hidden(sK7,sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_972,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,sK5)
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,sK5)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1330,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,sK3(sK5)),k2_zfmisc_1(X1,sK5))
    | ~ r2_hidden(sK3(sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_1662,plain,
    ( r2_hidden(k4_tarski(sK7,sK3(sK5)),k2_zfmisc_1(sK4,sK5))
    | ~ r2_hidden(sK3(sK5),sK5)
    | ~ r2_hidden(sK7,sK4) ),
    inference(instantiation,[status(thm)],[c_1330])).

cnf(c_1663,plain,
    ( r2_hidden(k4_tarski(sK7,sK3(sK5)),k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r2_hidden(sK3(sK5),sK5) != iProver_top
    | r2_hidden(sK7,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1662])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2867,plain,
    ( ~ r2_hidden(k4_tarski(sK7,sK3(sK5)),k2_zfmisc_1(sK4,sK5))
    | ~ v1_xboole_0(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2868,plain,
    ( r2_hidden(k4_tarski(sK7,sK3(sK5)),k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2867])).

cnf(c_2971,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2074,c_20,c_21,c_23,c_51,c_720,c_726,c_1663,c_2868])).

cnf(c_2972,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_2971])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_618,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2981,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2972,c_618])).

cnf(c_3208,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_622,c_2981])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_616,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3636,plain,
    ( m1_subset_1(sK2(sK6,X0),sK5) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3208,c_616])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_620,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1634,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_608,c_620])).

cnf(c_13,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(k4_tarski(sK7,X0),sK6)
    | ~ r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_612,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top
    | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1761,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top
    | r2_hidden(sK7,k1_relat_1(sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1634,c_612])).

cnf(c_2079,plain,
    ( m1_subset_1(sK2(sK6,sK7),sK5) != iProver_top
    | r2_hidden(sK7,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_622,c_1761])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(k4_tarski(sK7,sK8),sK6)
    | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_611,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),sK6) = iProver_top
    | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1759,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),sK6) = iProver_top
    | r2_hidden(sK7,k1_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1634,c_611])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_623,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2279,plain,
    ( r2_hidden(sK7,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1759,c_623])).

cnf(c_2961,plain,
    ( m1_subset_1(sK2(sK6,sK7),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2079,c_2279])).

cnf(c_4066,plain,
    ( r2_hidden(sK7,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3636,c_2961])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4066,c_2279])).


%------------------------------------------------------------------------------

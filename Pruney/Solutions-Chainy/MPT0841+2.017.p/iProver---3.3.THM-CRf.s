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
% DateTime   : Thu Dec  3 11:57:01 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 883 expanded)
%              Number of clauses        :   83 ( 261 expanded)
%              Number of leaves         :   23 ( 267 expanded)
%              Depth                    :   24
%              Number of atoms          :  570 (6470 expanded)
%              Number of equality atoms :  160 ( 423 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
            & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X5,X4),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <~> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X5,X4),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & ( ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) )
                        | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X5,X4),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & ( ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) )
                        | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X5,X4),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & ( ? [X6] :
                            ( r2_hidden(X6,X1)
                            & r2_hidden(k4_tarski(X6,X4),X3)
                            & m1_subset_1(X6,X2) )
                        | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(rectify,[],[f43])).

fof(f50,plain,(
    ! [X4,X2,X3,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK8,X1)
        & r2_hidden(k4_tarski(sK8,X4),X3)
        & m1_subset_1(sK8,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X5,X4),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,X1)
                & r2_hidden(k4_tarski(X6,X4),X3)
                & m1_subset_1(X6,X2) )
            | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & m1_subset_1(X4,X0) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(X5,X1)
              | ~ r2_hidden(k4_tarski(X5,sK7),X3)
              | ~ m1_subset_1(X5,X2) )
          | ~ r2_hidden(sK7,k7_relset_1(X2,X0,X3,X1)) )
        & ( ? [X6] :
              ( r2_hidden(X6,X1)
              & r2_hidden(k4_tarski(X6,sK7),X3)
              & m1_subset_1(X6,X2) )
          | r2_hidden(sK7,k7_relset_1(X2,X0,X3,X1)) )
        & m1_subset_1(sK7,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ! [X5] :
                    ( ~ r2_hidden(X5,X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X3)
                    | ~ m1_subset_1(X5,X2) )
                | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
              & ( ? [X6] :
                    ( r2_hidden(X6,X1)
                    & r2_hidden(k4_tarski(X6,X4),X3)
                    & m1_subset_1(X6,X2) )
                | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
              & m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
     => ( ? [X4] :
            ( ( ! [X5] :
                  ( ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(k4_tarski(X5,X4),sK6)
                  | ~ m1_subset_1(X5,X2) )
              | ~ r2_hidden(X4,k7_relset_1(X2,X0,sK6,X1)) )
            & ( ? [X6] :
                  ( r2_hidden(X6,X1)
                  & r2_hidden(k4_tarski(X6,X4),sK6)
                  & m1_subset_1(X6,X2) )
              | r2_hidden(X4,k7_relset_1(X2,X0,sK6,X1)) )
            & m1_subset_1(X4,X0) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ! [X5] :
                        ( ~ r2_hidden(X5,X1)
                        | ~ r2_hidden(k4_tarski(X5,X4),X3)
                        | ~ m1_subset_1(X5,X2) )
                    | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                  & ( ? [X6] :
                        ( r2_hidden(X6,X1)
                        & r2_hidden(k4_tarski(X6,X4),X3)
                        & m1_subset_1(X6,X2) )
                    | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
          & ~ v1_xboole_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ( ! [X5] :
                      ( ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(k4_tarski(X5,X4),X3)
                      | ~ m1_subset_1(X5,sK5) )
                  | ~ r2_hidden(X4,k7_relset_1(sK5,X0,X3,X1)) )
                & ( ? [X6] :
                      ( r2_hidden(X6,X1)
                      & r2_hidden(k4_tarski(X6,X4),X3)
                      & m1_subset_1(X6,sK5) )
                  | r2_hidden(X4,k7_relset_1(sK5,X0,X3,X1)) )
                & m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) )
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X5,X4),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & ( ? [X6] :
                            ( r2_hidden(X6,X1)
                            & r2_hidden(k4_tarski(X6,X4),X3)
                            & m1_subset_1(X6,X2) )
                        | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ! [X5] :
                          ( ~ r2_hidden(X5,sK4)
                          | ~ r2_hidden(k4_tarski(X5,X4),X3)
                          | ~ m1_subset_1(X5,X2) )
                      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,sK4)) )
                    & ( ? [X6] :
                          ( r2_hidden(X6,sK4)
                          & r2_hidden(k4_tarski(X6,X4),X3)
                          & m1_subset_1(X6,X2) )
                      | r2_hidden(X4,k7_relset_1(X2,X0,X3,sK4)) )
                    & m1_subset_1(X4,X0) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                        & ( ? [X6] :
                              ( r2_hidden(X6,X1)
                              & r2_hidden(k4_tarski(X6,X4),X3)
                              & m1_subset_1(X6,X2) )
                          | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                        & m1_subset_1(X4,X0) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
                & ~ v1_xboole_0(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X5,X4),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k7_relset_1(X2,sK3,X3,X1)) )
                      & ( ? [X6] :
                            ( r2_hidden(X6,X1)
                            & r2_hidden(k4_tarski(X6,X4),X3)
                            & m1_subset_1(X6,X2) )
                        | r2_hidden(X4,k7_relset_1(X2,sK3,X3,X1)) )
                      & m1_subset_1(X4,sK3) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK3))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ! [X5] :
          ( ~ r2_hidden(X5,sK4)
          | ~ r2_hidden(k4_tarski(X5,sK7),sK6)
          | ~ m1_subset_1(X5,sK5) )
      | ~ r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) )
    & ( ( r2_hidden(sK8,sK4)
        & r2_hidden(k4_tarski(sK8,sK7),sK6)
        & m1_subset_1(sK8,sK5) )
      | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) )
    & m1_subset_1(sK7,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    & ~ v1_xboole_0(sK5)
    & ~ v1_xboole_0(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f44,f50,f49,f48,f47,f46,f45])).

fof(f78,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f31])).

fof(f52,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k2_tarski(X0,X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f56])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f85,plain,(
    ! [X0,X1] : k2_xboole_0(k2_tarski(X0,X0),X1) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f58,f56])).

fof(f75,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,
    ( m1_subset_1(sK8,sK5)
    | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK4)
      | ~ r2_hidden(k4_tarski(X5,sK7),sK6)
      | ~ m1_subset_1(X5,sK5)
      | ~ r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,
    ( r2_hidden(k4_tarski(sK8,sK7),sK6)
    | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,
    ( r2_hidden(sK8,sK4)
    | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) ),
    inference(cnf_transformation,[],[f51])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1732,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK2(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_16,plain,
    ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1731,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1721,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1735,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2838,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK5,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1721,c_1735])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1739,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3878,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK5,sK3)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2838,c_1739])).

cnf(c_18,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1728,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4315,plain,
    ( r2_hidden(X0,k1_relat_1(k2_zfmisc_1(sK5,sK3))) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK5,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3878,c_1728])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1734,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6376,plain,
    ( r2_hidden(X0,k1_relat_1(k2_zfmisc_1(sK5,sK3))) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4315,c_1734])).

cnf(c_6380,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(X0,X1,sK6),k1_relat_1(k2_zfmisc_1(sK5,sK3))) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1731,c_6376])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_231,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_232,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_231])).

cnf(c_285,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_232])).

cnf(c_1718,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_285])).

cnf(c_5920,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK3)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2838,c_1718])).

cnf(c_6049,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5920,c_1734])).

cnf(c_9208,plain,
    ( r2_hidden(sK2(X0,X1,sK6),k1_relat_1(k2_zfmisc_1(sK5,sK3))) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6380,c_6049])).

cnf(c_9209,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(X0,X1,sK6),k1_relat_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_9208])).

cnf(c_9216,plain,
    ( sK3 = k1_xboole_0
    | sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(X0,X1,sK6),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_9209])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_385,plain,
    ( r2_hidden(sK0(X0),X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_28])).

cnf(c_386,plain,
    ( r2_hidden(sK0(sK5),sK5) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_1717,plain,
    ( r2_hidden(sK0(sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k2_tarski(X0,X0),X1) = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1738,plain,
    ( k2_xboole_0(k2_tarski(X0,X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3006,plain,
    ( k2_xboole_0(k2_tarski(sK0(sK5),sK0(sK5)),sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_1717,c_1738])).

cnf(c_5,plain,
    ( k2_xboole_0(k2_tarski(X0,X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4250,plain,
    ( sK5 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3006,c_5])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_399,plain,
    ( r2_hidden(sK0(X0),X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_30])).

cnf(c_400,plain,
    ( r2_hidden(sK0(sK3),sK3) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_1715,plain,
    ( r2_hidden(sK0(sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_3008,plain,
    ( k2_xboole_0(k2_tarski(sK0(sK3),sK0(sK3)),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1715,c_1738])).

cnf(c_4307,plain,
    ( sK3 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3008,c_5])).

cnf(c_9688,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(X0,X1,sK6),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9216,c_4250,c_4307])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1737,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9697,plain,
    ( m1_subset_1(sK2(X0,X1,sK6),sK5) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9688,c_1737])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK8,sK5)
    | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1723,plain,
    ( m1_subset_1(sK8,sK5) = iProver_top
    | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(k4_tarski(X0,sK7),sK6)
    | ~ r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1726,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top
    | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1994,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | m1_subset_1(sK8,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1723,c_1726])).

cnf(c_4584,plain,
    ( m1_subset_1(sK2(sK7,X0,sK6),sK5) != iProver_top
    | m1_subset_1(sK8,sK5) = iProver_top
    | r2_hidden(sK2(sK7,X0,sK6),sK4) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,X0)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1731,c_1994])).

cnf(c_9788,plain,
    ( m1_subset_1(sK8,sK5) = iProver_top
    | r2_hidden(sK2(sK7,X0,sK6),sK4) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,X0)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_9697,c_4584])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1727,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2729,plain,
    ( k7_relset_1(sK5,sK3,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_1721,c_1727])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(k4_tarski(sK8,sK7),sK6)
    | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1724,plain,
    ( r2_hidden(k4_tarski(sK8,sK7),sK6) = iProver_top
    | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3133,plain,
    ( r2_hidden(k4_tarski(sK8,sK7),sK6) = iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2729,c_1724])).

cnf(c_4312,plain,
    ( k2_xboole_0(k2_tarski(X0,X0),k2_zfmisc_1(sK5,sK3)) = k2_zfmisc_1(sK5,sK3)
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3878,c_1738])).

cnf(c_5772,plain,
    ( k2_xboole_0(k2_tarski(k4_tarski(sK8,sK7),k4_tarski(sK8,sK7)),k2_zfmisc_1(sK5,sK3)) = k2_zfmisc_1(sK5,sK3)
    | r2_hidden(sK7,k9_relat_1(sK6,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3133,c_4312])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK8,sK4)
    | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1725,plain,
    ( r2_hidden(sK8,sK4) = iProver_top
    | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3134,plain,
    ( r2_hidden(sK8,sK4) = iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2729,c_1725])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(X0,k1_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1733,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1875,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1733,c_1728])).

cnf(c_5075,plain,
    ( r2_hidden(sK8,X0) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,X0)) = iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK4)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3133,c_1875])).

cnf(c_5676,plain,
    ( r2_hidden(sK8,sK4) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK4)) = iProver_top
    | v1_relat_1(sK6) != iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_5075])).

cnf(c_5678,plain,
    ( r2_hidden(sK8,sK4) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK4)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5676])).

cnf(c_6114,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5772,c_3134,c_5678,c_6049])).

cnf(c_3136,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2729,c_1726])).

cnf(c_4581,plain,
    ( m1_subset_1(sK2(sK7,X0,sK6),sK5) != iProver_top
    | r2_hidden(sK2(sK7,X0,sK6),sK4) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,X0)) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK4)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1731,c_3136])).

cnf(c_9786,plain,
    ( r2_hidden(sK2(sK7,X0,sK6),sK4) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,X0)) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK4)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_9697,c_4581])).

cnf(c_9985,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,X0)) != iProver_top
    | r2_hidden(sK2(sK7,X0,sK6),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9788,c_3134,c_5678,c_6049,c_9786])).

cnf(c_9986,plain,
    ( r2_hidden(sK2(sK7,X0,sK6),sK4) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9985])).

cnf(c_9991,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK4)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1732,c_9986])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9991,c_6114,c_6049])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:17:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.47/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.47/0.99  
% 3.47/0.99  ------  iProver source info
% 3.47/0.99  
% 3.47/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.47/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.47/0.99  git: non_committed_changes: false
% 3.47/0.99  git: last_make_outside_of_git: false
% 3.47/0.99  
% 3.47/0.99  ------ 
% 3.47/0.99  
% 3.47/0.99  ------ Input Options
% 3.47/0.99  
% 3.47/0.99  --out_options                           all
% 3.47/0.99  --tptp_safe_out                         true
% 3.47/0.99  --problem_path                          ""
% 3.47/0.99  --include_path                          ""
% 3.47/0.99  --clausifier                            res/vclausify_rel
% 3.47/0.99  --clausifier_options                    --mode clausify
% 3.47/0.99  --stdin                                 false
% 3.47/0.99  --stats_out                             all
% 3.47/0.99  
% 3.47/0.99  ------ General Options
% 3.47/0.99  
% 3.47/0.99  --fof                                   false
% 3.47/0.99  --time_out_real                         305.
% 3.47/0.99  --time_out_virtual                      -1.
% 3.47/0.99  --symbol_type_check                     false
% 3.47/0.99  --clausify_out                          false
% 3.47/0.99  --sig_cnt_out                           false
% 3.47/0.99  --trig_cnt_out                          false
% 3.47/0.99  --trig_cnt_out_tolerance                1.
% 3.47/0.99  --trig_cnt_out_sk_spl                   false
% 3.47/0.99  --abstr_cl_out                          false
% 3.47/0.99  
% 3.47/0.99  ------ Global Options
% 3.47/0.99  
% 3.47/0.99  --schedule                              default
% 3.47/0.99  --add_important_lit                     false
% 3.47/0.99  --prop_solver_per_cl                    1000
% 3.47/0.99  --min_unsat_core                        false
% 3.47/0.99  --soft_assumptions                      false
% 3.47/0.99  --soft_lemma_size                       3
% 3.47/0.99  --prop_impl_unit_size                   0
% 3.47/0.99  --prop_impl_unit                        []
% 3.47/0.99  --share_sel_clauses                     true
% 3.47/0.99  --reset_solvers                         false
% 3.47/0.99  --bc_imp_inh                            [conj_cone]
% 3.47/0.99  --conj_cone_tolerance                   3.
% 3.47/0.99  --extra_neg_conj                        none
% 3.47/0.99  --large_theory_mode                     true
% 3.47/0.99  --prolific_symb_bound                   200
% 3.47/0.99  --lt_threshold                          2000
% 3.47/0.99  --clause_weak_htbl                      true
% 3.47/0.99  --gc_record_bc_elim                     false
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing Options
% 3.47/0.99  
% 3.47/0.99  --preprocessing_flag                    true
% 3.47/0.99  --time_out_prep_mult                    0.1
% 3.47/0.99  --splitting_mode                        input
% 3.47/0.99  --splitting_grd                         true
% 3.47/0.99  --splitting_cvd                         false
% 3.47/0.99  --splitting_cvd_svl                     false
% 3.47/0.99  --splitting_nvd                         32
% 3.47/0.99  --sub_typing                            true
% 3.47/0.99  --prep_gs_sim                           true
% 3.47/0.99  --prep_unflatten                        true
% 3.47/0.99  --prep_res_sim                          true
% 3.47/0.99  --prep_upred                            true
% 3.47/0.99  --prep_sem_filter                       exhaustive
% 3.47/0.99  --prep_sem_filter_out                   false
% 3.47/0.99  --pred_elim                             true
% 3.47/0.99  --res_sim_input                         true
% 3.47/0.99  --eq_ax_congr_red                       true
% 3.47/0.99  --pure_diseq_elim                       true
% 3.47/0.99  --brand_transform                       false
% 3.47/0.99  --non_eq_to_eq                          false
% 3.47/0.99  --prep_def_merge                        true
% 3.47/0.99  --prep_def_merge_prop_impl              false
% 3.47/0.99  --prep_def_merge_mbd                    true
% 3.47/0.99  --prep_def_merge_tr_red                 false
% 3.47/0.99  --prep_def_merge_tr_cl                  false
% 3.47/0.99  --smt_preprocessing                     true
% 3.47/0.99  --smt_ac_axioms                         fast
% 3.47/0.99  --preprocessed_out                      false
% 3.47/0.99  --preprocessed_stats                    false
% 3.47/0.99  
% 3.47/0.99  ------ Abstraction refinement Options
% 3.47/0.99  
% 3.47/0.99  --abstr_ref                             []
% 3.47/0.99  --abstr_ref_prep                        false
% 3.47/0.99  --abstr_ref_until_sat                   false
% 3.47/0.99  --abstr_ref_sig_restrict                funpre
% 3.47/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.47/0.99  --abstr_ref_under                       []
% 3.47/0.99  
% 3.47/0.99  ------ SAT Options
% 3.47/0.99  
% 3.47/0.99  --sat_mode                              false
% 3.47/0.99  --sat_fm_restart_options                ""
% 3.47/0.99  --sat_gr_def                            false
% 3.47/0.99  --sat_epr_types                         true
% 3.47/0.99  --sat_non_cyclic_types                  false
% 3.47/0.99  --sat_finite_models                     false
% 3.47/0.99  --sat_fm_lemmas                         false
% 3.47/0.99  --sat_fm_prep                           false
% 3.47/0.99  --sat_fm_uc_incr                        true
% 3.47/0.99  --sat_out_model                         small
% 3.47/0.99  --sat_out_clauses                       false
% 3.47/0.99  
% 3.47/0.99  ------ QBF Options
% 3.47/0.99  
% 3.47/0.99  --qbf_mode                              false
% 3.47/0.99  --qbf_elim_univ                         false
% 3.47/0.99  --qbf_dom_inst                          none
% 3.47/0.99  --qbf_dom_pre_inst                      false
% 3.47/0.99  --qbf_sk_in                             false
% 3.47/0.99  --qbf_pred_elim                         true
% 3.47/0.99  --qbf_split                             512
% 3.47/0.99  
% 3.47/0.99  ------ BMC1 Options
% 3.47/0.99  
% 3.47/0.99  --bmc1_incremental                      false
% 3.47/0.99  --bmc1_axioms                           reachable_all
% 3.47/0.99  --bmc1_min_bound                        0
% 3.47/0.99  --bmc1_max_bound                        -1
% 3.47/0.99  --bmc1_max_bound_default                -1
% 3.47/0.99  --bmc1_symbol_reachability              true
% 3.47/0.99  --bmc1_property_lemmas                  false
% 3.47/0.99  --bmc1_k_induction                      false
% 3.47/0.99  --bmc1_non_equiv_states                 false
% 3.47/0.99  --bmc1_deadlock                         false
% 3.47/0.99  --bmc1_ucm                              false
% 3.47/0.99  --bmc1_add_unsat_core                   none
% 3.47/0.99  --bmc1_unsat_core_children              false
% 3.47/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.47/0.99  --bmc1_out_stat                         full
% 3.47/0.99  --bmc1_ground_init                      false
% 3.47/0.99  --bmc1_pre_inst_next_state              false
% 3.47/0.99  --bmc1_pre_inst_state                   false
% 3.47/0.99  --bmc1_pre_inst_reach_state             false
% 3.47/0.99  --bmc1_out_unsat_core                   false
% 3.47/0.99  --bmc1_aig_witness_out                  false
% 3.47/0.99  --bmc1_verbose                          false
% 3.47/0.99  --bmc1_dump_clauses_tptp                false
% 3.47/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.47/0.99  --bmc1_dump_file                        -
% 3.47/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.47/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.47/0.99  --bmc1_ucm_extend_mode                  1
% 3.47/0.99  --bmc1_ucm_init_mode                    2
% 3.47/0.99  --bmc1_ucm_cone_mode                    none
% 3.47/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.47/0.99  --bmc1_ucm_relax_model                  4
% 3.47/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.47/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.47/0.99  --bmc1_ucm_layered_model                none
% 3.47/0.99  --bmc1_ucm_max_lemma_size               10
% 3.47/0.99  
% 3.47/0.99  ------ AIG Options
% 3.47/0.99  
% 3.47/0.99  --aig_mode                              false
% 3.47/0.99  
% 3.47/0.99  ------ Instantiation Options
% 3.47/0.99  
% 3.47/0.99  --instantiation_flag                    true
% 3.47/0.99  --inst_sos_flag                         false
% 3.47/0.99  --inst_sos_phase                        true
% 3.47/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.47/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.47/0.99  --inst_lit_sel_side                     num_symb
% 3.47/0.99  --inst_solver_per_active                1400
% 3.47/0.99  --inst_solver_calls_frac                1.
% 3.47/0.99  --inst_passive_queue_type               priority_queues
% 3.47/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.47/0.99  --inst_passive_queues_freq              [25;2]
% 3.47/0.99  --inst_dismatching                      true
% 3.47/0.99  --inst_eager_unprocessed_to_passive     true
% 3.47/0.99  --inst_prop_sim_given                   true
% 3.47/0.99  --inst_prop_sim_new                     false
% 3.47/0.99  --inst_subs_new                         false
% 3.47/0.99  --inst_eq_res_simp                      false
% 3.47/0.99  --inst_subs_given                       false
% 3.47/0.99  --inst_orphan_elimination               true
% 3.47/0.99  --inst_learning_loop_flag               true
% 3.47/0.99  --inst_learning_start                   3000
% 3.47/0.99  --inst_learning_factor                  2
% 3.47/0.99  --inst_start_prop_sim_after_learn       3
% 3.47/0.99  --inst_sel_renew                        solver
% 3.47/0.99  --inst_lit_activity_flag                true
% 3.47/0.99  --inst_restr_to_given                   false
% 3.47/0.99  --inst_activity_threshold               500
% 3.47/0.99  --inst_out_proof                        true
% 3.47/0.99  
% 3.47/0.99  ------ Resolution Options
% 3.47/0.99  
% 3.47/0.99  --resolution_flag                       true
% 3.47/0.99  --res_lit_sel                           adaptive
% 3.47/0.99  --res_lit_sel_side                      none
% 3.47/0.99  --res_ordering                          kbo
% 3.47/0.99  --res_to_prop_solver                    active
% 3.47/0.99  --res_prop_simpl_new                    false
% 3.47/0.99  --res_prop_simpl_given                  true
% 3.47/0.99  --res_passive_queue_type                priority_queues
% 3.47/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.47/0.99  --res_passive_queues_freq               [15;5]
% 3.47/0.99  --res_forward_subs                      full
% 3.47/0.99  --res_backward_subs                     full
% 3.47/0.99  --res_forward_subs_resolution           true
% 3.47/0.99  --res_backward_subs_resolution          true
% 3.47/0.99  --res_orphan_elimination                true
% 3.47/0.99  --res_time_limit                        2.
% 3.47/0.99  --res_out_proof                         true
% 3.47/0.99  
% 3.47/0.99  ------ Superposition Options
% 3.47/0.99  
% 3.47/0.99  --superposition_flag                    true
% 3.47/0.99  --sup_passive_queue_type                priority_queues
% 3.47/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.47/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.47/0.99  --demod_completeness_check              fast
% 3.47/0.99  --demod_use_ground                      true
% 3.47/0.99  --sup_to_prop_solver                    passive
% 3.47/0.99  --sup_prop_simpl_new                    true
% 3.47/0.99  --sup_prop_simpl_given                  true
% 3.47/0.99  --sup_fun_splitting                     false
% 3.47/0.99  --sup_smt_interval                      50000
% 3.47/0.99  
% 3.47/0.99  ------ Superposition Simplification Setup
% 3.47/0.99  
% 3.47/0.99  --sup_indices_passive                   []
% 3.47/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.47/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/0.99  --sup_full_bw                           [BwDemod]
% 3.47/0.99  --sup_immed_triv                        [TrivRules]
% 3.47/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.47/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/0.99  --sup_immed_bw_main                     []
% 3.47/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.47/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/0.99  
% 3.47/0.99  ------ Combination Options
% 3.47/0.99  
% 3.47/0.99  --comb_res_mult                         3
% 3.47/0.99  --comb_sup_mult                         2
% 3.47/0.99  --comb_inst_mult                        10
% 3.47/0.99  
% 3.47/0.99  ------ Debug Options
% 3.47/0.99  
% 3.47/0.99  --dbg_backtrace                         false
% 3.47/0.99  --dbg_dump_prop_clauses                 false
% 3.47/0.99  --dbg_dump_prop_clauses_file            -
% 3.47/0.99  --dbg_out_stat                          false
% 3.47/0.99  ------ Parsing...
% 3.47/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  ------ Proving...
% 3.47/0.99  ------ Problem Properties 
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  clauses                                 30
% 3.47/0.99  conjectures                             6
% 3.47/0.99  EPR                                     4
% 3.47/0.99  Horn                                    24
% 3.47/0.99  unary                                   7
% 3.47/0.99  binary                                  10
% 3.47/0.99  lits                                    69
% 3.47/0.99  lits eq                                 9
% 3.47/0.99  fd_pure                                 0
% 3.47/0.99  fd_pseudo                               0
% 3.47/0.99  fd_cond                                 0
% 3.47/0.99  fd_pseudo_cond                          0
% 3.47/0.99  AC symbols                              0
% 3.47/0.99  
% 3.47/0.99  ------ Schedule dynamic 5 is on 
% 3.47/0.99  
% 3.47/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ 
% 3.47/0.99  Current options:
% 3.47/0.99  ------ 
% 3.47/0.99  
% 3.47/0.99  ------ Input Options
% 3.47/0.99  
% 3.47/0.99  --out_options                           all
% 3.47/0.99  --tptp_safe_out                         true
% 3.47/0.99  --problem_path                          ""
% 3.47/0.99  --include_path                          ""
% 3.47/0.99  --clausifier                            res/vclausify_rel
% 3.47/0.99  --clausifier_options                    --mode clausify
% 3.47/0.99  --stdin                                 false
% 3.47/0.99  --stats_out                             all
% 3.47/0.99  
% 3.47/0.99  ------ General Options
% 3.47/0.99  
% 3.47/0.99  --fof                                   false
% 3.47/0.99  --time_out_real                         305.
% 3.47/0.99  --time_out_virtual                      -1.
% 3.47/0.99  --symbol_type_check                     false
% 3.47/0.99  --clausify_out                          false
% 3.47/0.99  --sig_cnt_out                           false
% 3.47/0.99  --trig_cnt_out                          false
% 3.47/0.99  --trig_cnt_out_tolerance                1.
% 3.47/0.99  --trig_cnt_out_sk_spl                   false
% 3.47/0.99  --abstr_cl_out                          false
% 3.47/0.99  
% 3.47/0.99  ------ Global Options
% 3.47/0.99  
% 3.47/0.99  --schedule                              default
% 3.47/0.99  --add_important_lit                     false
% 3.47/0.99  --prop_solver_per_cl                    1000
% 3.47/0.99  --min_unsat_core                        false
% 3.47/0.99  --soft_assumptions                      false
% 3.47/0.99  --soft_lemma_size                       3
% 3.47/0.99  --prop_impl_unit_size                   0
% 3.47/0.99  --prop_impl_unit                        []
% 3.47/0.99  --share_sel_clauses                     true
% 3.47/0.99  --reset_solvers                         false
% 3.47/0.99  --bc_imp_inh                            [conj_cone]
% 3.47/0.99  --conj_cone_tolerance                   3.
% 3.47/0.99  --extra_neg_conj                        none
% 3.47/0.99  --large_theory_mode                     true
% 3.47/0.99  --prolific_symb_bound                   200
% 3.47/0.99  --lt_threshold                          2000
% 3.47/0.99  --clause_weak_htbl                      true
% 3.47/0.99  --gc_record_bc_elim                     false
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing Options
% 3.47/0.99  
% 3.47/0.99  --preprocessing_flag                    true
% 3.47/0.99  --time_out_prep_mult                    0.1
% 3.47/0.99  --splitting_mode                        input
% 3.47/0.99  --splitting_grd                         true
% 3.47/0.99  --splitting_cvd                         false
% 3.47/0.99  --splitting_cvd_svl                     false
% 3.47/0.99  --splitting_nvd                         32
% 3.47/0.99  --sub_typing                            true
% 3.47/0.99  --prep_gs_sim                           true
% 3.47/0.99  --prep_unflatten                        true
% 3.47/0.99  --prep_res_sim                          true
% 3.47/0.99  --prep_upred                            true
% 3.47/0.99  --prep_sem_filter                       exhaustive
% 3.47/0.99  --prep_sem_filter_out                   false
% 3.47/0.99  --pred_elim                             true
% 3.47/0.99  --res_sim_input                         true
% 3.47/0.99  --eq_ax_congr_red                       true
% 3.47/0.99  --pure_diseq_elim                       true
% 3.47/0.99  --brand_transform                       false
% 3.47/0.99  --non_eq_to_eq                          false
% 3.47/0.99  --prep_def_merge                        true
% 3.47/0.99  --prep_def_merge_prop_impl              false
% 3.47/0.99  --prep_def_merge_mbd                    true
% 3.47/0.99  --prep_def_merge_tr_red                 false
% 3.47/0.99  --prep_def_merge_tr_cl                  false
% 3.47/0.99  --smt_preprocessing                     true
% 3.47/0.99  --smt_ac_axioms                         fast
% 3.47/0.99  --preprocessed_out                      false
% 3.47/0.99  --preprocessed_stats                    false
% 3.47/0.99  
% 3.47/0.99  ------ Abstraction refinement Options
% 3.47/0.99  
% 3.47/0.99  --abstr_ref                             []
% 3.47/0.99  --abstr_ref_prep                        false
% 3.47/0.99  --abstr_ref_until_sat                   false
% 3.47/0.99  --abstr_ref_sig_restrict                funpre
% 3.47/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.47/0.99  --abstr_ref_under                       []
% 3.47/0.99  
% 3.47/0.99  ------ SAT Options
% 3.47/0.99  
% 3.47/0.99  --sat_mode                              false
% 3.47/0.99  --sat_fm_restart_options                ""
% 3.47/0.99  --sat_gr_def                            false
% 3.47/0.99  --sat_epr_types                         true
% 3.47/0.99  --sat_non_cyclic_types                  false
% 3.47/0.99  --sat_finite_models                     false
% 3.47/0.99  --sat_fm_lemmas                         false
% 3.47/0.99  --sat_fm_prep                           false
% 3.47/0.99  --sat_fm_uc_incr                        true
% 3.47/0.99  --sat_out_model                         small
% 3.47/0.99  --sat_out_clauses                       false
% 3.47/0.99  
% 3.47/0.99  ------ QBF Options
% 3.47/0.99  
% 3.47/0.99  --qbf_mode                              false
% 3.47/0.99  --qbf_elim_univ                         false
% 3.47/0.99  --qbf_dom_inst                          none
% 3.47/0.99  --qbf_dom_pre_inst                      false
% 3.47/0.99  --qbf_sk_in                             false
% 3.47/0.99  --qbf_pred_elim                         true
% 3.47/0.99  --qbf_split                             512
% 3.47/0.99  
% 3.47/0.99  ------ BMC1 Options
% 3.47/0.99  
% 3.47/0.99  --bmc1_incremental                      false
% 3.47/0.99  --bmc1_axioms                           reachable_all
% 3.47/0.99  --bmc1_min_bound                        0
% 3.47/0.99  --bmc1_max_bound                        -1
% 3.47/0.99  --bmc1_max_bound_default                -1
% 3.47/0.99  --bmc1_symbol_reachability              true
% 3.47/0.99  --bmc1_property_lemmas                  false
% 3.47/0.99  --bmc1_k_induction                      false
% 3.47/0.99  --bmc1_non_equiv_states                 false
% 3.47/0.99  --bmc1_deadlock                         false
% 3.47/0.99  --bmc1_ucm                              false
% 3.47/0.99  --bmc1_add_unsat_core                   none
% 3.47/0.99  --bmc1_unsat_core_children              false
% 3.47/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.47/0.99  --bmc1_out_stat                         full
% 3.47/0.99  --bmc1_ground_init                      false
% 3.47/0.99  --bmc1_pre_inst_next_state              false
% 3.47/0.99  --bmc1_pre_inst_state                   false
% 3.47/0.99  --bmc1_pre_inst_reach_state             false
% 3.47/0.99  --bmc1_out_unsat_core                   false
% 3.47/0.99  --bmc1_aig_witness_out                  false
% 3.47/0.99  --bmc1_verbose                          false
% 3.47/0.99  --bmc1_dump_clauses_tptp                false
% 3.47/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.47/0.99  --bmc1_dump_file                        -
% 3.47/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.47/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.47/0.99  --bmc1_ucm_extend_mode                  1
% 3.47/0.99  --bmc1_ucm_init_mode                    2
% 3.47/0.99  --bmc1_ucm_cone_mode                    none
% 3.47/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.47/0.99  --bmc1_ucm_relax_model                  4
% 3.47/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.47/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.47/0.99  --bmc1_ucm_layered_model                none
% 3.47/0.99  --bmc1_ucm_max_lemma_size               10
% 3.47/0.99  
% 3.47/0.99  ------ AIG Options
% 3.47/0.99  
% 3.47/0.99  --aig_mode                              false
% 3.47/0.99  
% 3.47/0.99  ------ Instantiation Options
% 3.47/0.99  
% 3.47/0.99  --instantiation_flag                    true
% 3.47/0.99  --inst_sos_flag                         false
% 3.47/0.99  --inst_sos_phase                        true
% 3.47/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.47/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.47/0.99  --inst_lit_sel_side                     none
% 3.47/0.99  --inst_solver_per_active                1400
% 3.47/0.99  --inst_solver_calls_frac                1.
% 3.47/0.99  --inst_passive_queue_type               priority_queues
% 3.47/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.47/0.99  --inst_passive_queues_freq              [25;2]
% 3.47/0.99  --inst_dismatching                      true
% 3.47/0.99  --inst_eager_unprocessed_to_passive     true
% 3.47/0.99  --inst_prop_sim_given                   true
% 3.47/0.99  --inst_prop_sim_new                     false
% 3.47/0.99  --inst_subs_new                         false
% 3.47/0.99  --inst_eq_res_simp                      false
% 3.47/0.99  --inst_subs_given                       false
% 3.47/0.99  --inst_orphan_elimination               true
% 3.47/0.99  --inst_learning_loop_flag               true
% 3.47/0.99  --inst_learning_start                   3000
% 3.47/0.99  --inst_learning_factor                  2
% 3.47/0.99  --inst_start_prop_sim_after_learn       3
% 3.47/0.99  --inst_sel_renew                        solver
% 3.47/0.99  --inst_lit_activity_flag                true
% 3.47/0.99  --inst_restr_to_given                   false
% 3.47/0.99  --inst_activity_threshold               500
% 3.47/0.99  --inst_out_proof                        true
% 3.47/0.99  
% 3.47/0.99  ------ Resolution Options
% 3.47/0.99  
% 3.47/0.99  --resolution_flag                       false
% 3.47/0.99  --res_lit_sel                           adaptive
% 3.47/0.99  --res_lit_sel_side                      none
% 3.47/0.99  --res_ordering                          kbo
% 3.47/0.99  --res_to_prop_solver                    active
% 3.47/0.99  --res_prop_simpl_new                    false
% 3.47/0.99  --res_prop_simpl_given                  true
% 3.47/0.99  --res_passive_queue_type                priority_queues
% 3.47/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.47/0.99  --res_passive_queues_freq               [15;5]
% 3.47/0.99  --res_forward_subs                      full
% 3.47/0.99  --res_backward_subs                     full
% 3.47/0.99  --res_forward_subs_resolution           true
% 3.47/0.99  --res_backward_subs_resolution          true
% 3.47/0.99  --res_orphan_elimination                true
% 3.47/0.99  --res_time_limit                        2.
% 3.47/0.99  --res_out_proof                         true
% 3.47/0.99  
% 3.47/0.99  ------ Superposition Options
% 3.47/0.99  
% 3.47/0.99  --superposition_flag                    true
% 3.47/0.99  --sup_passive_queue_type                priority_queues
% 3.47/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.47/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.47/0.99  --demod_completeness_check              fast
% 3.47/0.99  --demod_use_ground                      true
% 3.47/0.99  --sup_to_prop_solver                    passive
% 3.47/0.99  --sup_prop_simpl_new                    true
% 3.47/0.99  --sup_prop_simpl_given                  true
% 3.47/0.99  --sup_fun_splitting                     false
% 3.47/0.99  --sup_smt_interval                      50000
% 3.47/0.99  
% 3.47/0.99  ------ Superposition Simplification Setup
% 3.47/0.99  
% 3.47/0.99  --sup_indices_passive                   []
% 3.47/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.47/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/0.99  --sup_full_bw                           [BwDemod]
% 3.47/0.99  --sup_immed_triv                        [TrivRules]
% 3.47/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.47/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/0.99  --sup_immed_bw_main                     []
% 3.47/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.47/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/0.99  
% 3.47/0.99  ------ Combination Options
% 3.47/0.99  
% 3.47/0.99  --comb_res_mult                         3
% 3.47/0.99  --comb_sup_mult                         2
% 3.47/0.99  --comb_inst_mult                        10
% 3.47/0.99  
% 3.47/0.99  ------ Debug Options
% 3.47/0.99  
% 3.47/0.99  --dbg_backtrace                         false
% 3.47/0.99  --dbg_dump_prop_clauses                 false
% 3.47/0.99  --dbg_dump_prop_clauses_file            -
% 3.47/0.99  --dbg_out_stat                          false
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  % SZS status Theorem for theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  fof(f10,axiom,(
% 3.47/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f23,plain,(
% 3.47/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.47/0.99    inference(ennf_transformation,[],[f10])).
% 3.47/0.99  
% 3.47/0.99  fof(f38,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.47/0.99    inference(nnf_transformation,[],[f23])).
% 3.47/0.99  
% 3.47/0.99  fof(f39,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.47/0.99    inference(rectify,[],[f38])).
% 3.47/0.99  
% 3.47/0.99  fof(f40,plain,(
% 3.47/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))))),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f41,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 3.47/0.99  
% 3.47/0.99  fof(f66,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f41])).
% 3.47/0.99  
% 3.47/0.99  fof(f11,axiom,(
% 3.47/0.99    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f24,plain,(
% 3.47/0.99    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.47/0.99    inference(ennf_transformation,[],[f11])).
% 3.47/0.99  
% 3.47/0.99  fof(f68,plain,(
% 3.47/0.99    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.47/0.99    inference(cnf_transformation,[],[f24])).
% 3.47/0.99  
% 3.47/0.99  fof(f65,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f41])).
% 3.47/0.99  
% 3.47/0.99  fof(f15,conjecture,(
% 3.47/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f16,negated_conjecture,(
% 3.47/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 3.47/0.99    inference(negated_conjecture,[],[f15])).
% 3.47/0.99  
% 3.47/0.99  fof(f30,plain,(
% 3.47/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.47/0.99    inference(ennf_transformation,[],[f16])).
% 3.47/0.99  
% 3.47/0.99  fof(f42,plain,(
% 3.47/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.47/0.99    inference(nnf_transformation,[],[f30])).
% 3.47/0.99  
% 3.47/0.99  fof(f43,plain,(
% 3.47/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.47/0.99    inference(flattening,[],[f42])).
% 3.47/0.99  
% 3.47/0.99  fof(f44,plain,(
% 3.47/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.47/0.99    inference(rectify,[],[f43])).
% 3.47/0.99  
% 3.47/0.99  fof(f50,plain,(
% 3.47/0.99    ( ! [X4,X2,X3,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK8,X1) & r2_hidden(k4_tarski(sK8,X4),X3) & m1_subset_1(sK8,X2))) )),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f49,plain,(
% 3.47/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) => ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,sK7),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(sK7,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,sK7),X3) & m1_subset_1(X6,X2)) | r2_hidden(sK7,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(sK7,X0))) )),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f48,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),sK6) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,sK6,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),sK6) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,sK6,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))) )),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f47,plain,(
% 3.47/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,sK5)) | ~r2_hidden(X4,k7_relset_1(sK5,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,sK5)) | r2_hidden(X4,k7_relset_1(sK5,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X0)))) & ~v1_xboole_0(sK5))) )),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f46,plain,(
% 3.47/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,sK4) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,sK4))) & (? [X6] : (r2_hidden(X6,sK4) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,sK4))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK4))) )),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f45,plain,(
% 3.47/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,sK3,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,sK3,X3,X1))) & m1_subset_1(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK3)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK3))),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f51,plain,(
% 3.47/0.99    (((((! [X5] : (~r2_hidden(X5,sK4) | ~r2_hidden(k4_tarski(X5,sK7),sK6) | ~m1_subset_1(X5,sK5)) | ~r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4))) & ((r2_hidden(sK8,sK4) & r2_hidden(k4_tarski(sK8,sK7),sK6) & m1_subset_1(sK8,sK5)) | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4))) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))) & ~v1_xboole_0(sK5)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)),
% 3.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f44,f50,f49,f48,f47,f46,f45])).
% 3.47/0.99  
% 3.47/0.99  fof(f78,plain,(
% 3.47/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f7,axiom,(
% 3.47/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f37,plain,(
% 3.47/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.47/0.99    inference(nnf_transformation,[],[f7])).
% 3.47/0.99  
% 3.47/0.99  fof(f60,plain,(
% 3.47/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.47/0.99    inference(cnf_transformation,[],[f37])).
% 3.47/0.99  
% 3.47/0.99  fof(f2,axiom,(
% 3.47/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f19,plain,(
% 3.47/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.47/0.99    inference(ennf_transformation,[],[f2])).
% 3.47/0.99  
% 3.47/0.99  fof(f33,plain,(
% 3.47/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.47/0.99    inference(nnf_transformation,[],[f19])).
% 3.47/0.99  
% 3.47/0.99  fof(f34,plain,(
% 3.47/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.47/0.99    inference(rectify,[],[f33])).
% 3.47/0.99  
% 3.47/0.99  fof(f35,plain,(
% 3.47/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f36,plain,(
% 3.47/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 3.47/0.99  
% 3.47/0.99  fof(f53,plain,(
% 3.47/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f36])).
% 3.47/0.99  
% 3.47/0.99  fof(f12,axiom,(
% 3.47/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f25,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 3.47/0.99    inference(ennf_transformation,[],[f12])).
% 3.47/0.99  
% 3.47/0.99  fof(f26,plain,(
% 3.47/0.99    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 3.47/0.99    inference(flattening,[],[f25])).
% 3.47/0.99  
% 3.47/0.99  fof(f70,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f26])).
% 3.47/0.99  
% 3.47/0.99  fof(f9,axiom,(
% 3.47/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f63,plain,(
% 3.47/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.47/0.99    inference(cnf_transformation,[],[f9])).
% 3.47/0.99  
% 3.47/0.99  fof(f8,axiom,(
% 3.47/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f22,plain,(
% 3.47/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.47/0.99    inference(ennf_transformation,[],[f8])).
% 3.47/0.99  
% 3.47/0.99  fof(f62,plain,(
% 3.47/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f22])).
% 3.47/0.99  
% 3.47/0.99  fof(f61,plain,(
% 3.47/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f37])).
% 3.47/0.99  
% 3.47/0.99  fof(f1,axiom,(
% 3.47/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f17,plain,(
% 3.47/0.99    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 3.47/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 3.47/0.99  
% 3.47/0.99  fof(f18,plain,(
% 3.47/0.99    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 3.47/0.99    inference(ennf_transformation,[],[f17])).
% 3.47/0.99  
% 3.47/0.99  fof(f31,plain,(
% 3.47/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f32,plain,(
% 3.47/0.99    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 3.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f31])).
% 3.47/0.99  
% 3.47/0.99  fof(f52,plain,(
% 3.47/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f32])).
% 3.47/0.99  
% 3.47/0.99  fof(f77,plain,(
% 3.47/0.99    ~v1_xboole_0(sK5)),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f4,axiom,(
% 3.47/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f20,plain,(
% 3.47/0.99    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 3.47/0.99    inference(ennf_transformation,[],[f4])).
% 3.47/0.99  
% 3.47/0.99  fof(f57,plain,(
% 3.47/0.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f20])).
% 3.47/0.99  
% 3.47/0.99  fof(f3,axiom,(
% 3.47/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f56,plain,(
% 3.47/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f3])).
% 3.47/0.99  
% 3.47/0.99  fof(f84,plain,(
% 3.47/0.99    ( ! [X0,X1] : (k2_xboole_0(k2_tarski(X0,X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 3.47/0.99    inference(definition_unfolding,[],[f57,f56])).
% 3.47/0.99  
% 3.47/0.99  fof(f5,axiom,(
% 3.47/0.99    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f58,plain,(
% 3.47/0.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 3.47/0.99    inference(cnf_transformation,[],[f5])).
% 3.47/0.99  
% 3.47/0.99  fof(f85,plain,(
% 3.47/0.99    ( ! [X0,X1] : (k2_xboole_0(k2_tarski(X0,X0),X1) != k1_xboole_0) )),
% 3.47/0.99    inference(definition_unfolding,[],[f58,f56])).
% 3.47/0.99  
% 3.47/0.99  fof(f75,plain,(
% 3.47/0.99    ~v1_xboole_0(sK3)),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f6,axiom,(
% 3.47/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f21,plain,(
% 3.47/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.47/0.99    inference(ennf_transformation,[],[f6])).
% 3.47/0.99  
% 3.47/0.99  fof(f59,plain,(
% 3.47/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f21])).
% 3.47/0.99  
% 3.47/0.99  fof(f80,plain,(
% 3.47/0.99    m1_subset_1(sK8,sK5) | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4))),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f83,plain,(
% 3.47/0.99    ( ! [X5] : (~r2_hidden(X5,sK4) | ~r2_hidden(k4_tarski(X5,sK7),sK6) | ~m1_subset_1(X5,sK5) | ~r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4))) )),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f14,axiom,(
% 3.47/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f29,plain,(
% 3.47/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.47/0.99    inference(ennf_transformation,[],[f14])).
% 3.47/0.99  
% 3.47/0.99  fof(f74,plain,(
% 3.47/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.47/0.99    inference(cnf_transformation,[],[f29])).
% 3.47/0.99  
% 3.47/0.99  fof(f81,plain,(
% 3.47/0.99    r2_hidden(k4_tarski(sK8,sK7),sK6) | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4))),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f82,plain,(
% 3.47/0.99    r2_hidden(sK8,sK4) | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4))),
% 3.47/0.99    inference(cnf_transformation,[],[f51])).
% 3.47/0.99  
% 3.47/0.99  fof(f67,plain,(
% 3.47/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k9_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f41])).
% 3.47/0.99  
% 3.47/0.99  cnf(c_12,plain,
% 3.47/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.47/0.99      | r2_hidden(sK2(X0,X2,X1),X2)
% 3.47/0.99      | ~ v1_relat_1(X1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1732,plain,
% 3.47/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.47/0.99      | r2_hidden(sK2(X0,X2,X1),X2) = iProver_top
% 3.47/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_16,plain,
% 3.47/0.99      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
% 3.47/0.99      | k1_xboole_0 = X1
% 3.47/0.99      | k1_xboole_0 = X0 ),
% 3.47/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_13,plain,
% 3.47/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.47/0.99      | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
% 3.47/0.99      | ~ v1_relat_1(X1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1731,plain,
% 3.47/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.47/0.99      | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1) = iProver_top
% 3.47/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_27,negated_conjecture,
% 3.47/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 3.47/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1721,plain,
% 3.47/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_8,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1735,plain,
% 3.47/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.47/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2838,plain,
% 3.47/0.99      ( r1_tarski(sK6,k2_zfmisc_1(sK5,sK3)) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1721,c_1735]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3,plain,
% 3.47/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1739,plain,
% 3.47/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.47/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.47/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3878,plain,
% 3.47/0.99      ( r2_hidden(X0,k2_zfmisc_1(sK5,sK3)) = iProver_top
% 3.47/0.99      | r2_hidden(X0,sK6) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_2838,c_1739]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_18,plain,
% 3.47/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 3.47/0.99      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.47/0.99      | ~ v1_relat_1(X1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1728,plain,
% 3.47/0.99      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 3.47/0.99      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
% 3.47/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4315,plain,
% 3.47/0.99      ( r2_hidden(X0,k1_relat_1(k2_zfmisc_1(sK5,sK3))) = iProver_top
% 3.47/0.99      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 3.47/0.99      | v1_relat_1(k2_zfmisc_1(sK5,sK3)) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_3878,c_1728]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_10,plain,
% 3.47/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1734,plain,
% 3.47/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6376,plain,
% 3.47/0.99      ( r2_hidden(X0,k1_relat_1(k2_zfmisc_1(sK5,sK3))) = iProver_top
% 3.47/0.99      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
% 3.47/0.99      inference(forward_subsumption_resolution,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_4315,c_1734]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6380,plain,
% 3.47/0.99      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.47/0.99      | r2_hidden(sK2(X0,X1,sK6),k1_relat_1(k2_zfmisc_1(sK5,sK3))) = iProver_top
% 3.47/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1731,c_6376]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_9,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.47/0.99      | ~ v1_relat_1(X1)
% 3.47/0.99      | v1_relat_1(X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7,plain,
% 3.47/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_231,plain,
% 3.47/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.47/0.99      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_232,plain,
% 3.47/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.47/0.99      inference(renaming,[status(thm)],[c_231]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_285,plain,
% 3.47/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.47/0.99      inference(bin_hyper_res,[status(thm)],[c_9,c_232]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1718,plain,
% 3.47/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.47/0.99      | v1_relat_1(X1) != iProver_top
% 3.47/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_285]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_5920,plain,
% 3.47/0.99      ( v1_relat_1(k2_zfmisc_1(sK5,sK3)) != iProver_top
% 3.47/0.99      | v1_relat_1(sK6) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_2838,c_1718]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6049,plain,
% 3.47/0.99      ( v1_relat_1(sK6) = iProver_top ),
% 3.47/0.99      inference(forward_subsumption_resolution,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_5920,c_1734]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_9208,plain,
% 3.47/0.99      ( r2_hidden(sK2(X0,X1,sK6),k1_relat_1(k2_zfmisc_1(sK5,sK3))) = iProver_top
% 3.47/0.99      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_6380,c_6049]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_9209,plain,
% 3.47/0.99      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.47/0.99      | r2_hidden(sK2(X0,X1,sK6),k1_relat_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 3.47/0.99      inference(renaming,[status(thm)],[c_9208]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_9216,plain,
% 3.47/0.99      ( sK3 = k1_xboole_0
% 3.47/0.99      | sK5 = k1_xboole_0
% 3.47/0.99      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.47/0.99      | r2_hidden(sK2(X0,X1,sK6),sK5) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_16,c_9209]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_0,plain,
% 3.47/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_28,negated_conjecture,
% 3.47/0.99      ( ~ v1_xboole_0(sK5) ),
% 3.47/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_385,plain,
% 3.47/0.99      ( r2_hidden(sK0(X0),X0) | sK5 != X0 ),
% 3.47/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_28]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_386,plain,
% 3.47/0.99      ( r2_hidden(sK0(sK5),sK5) ),
% 3.47/0.99      inference(unflattening,[status(thm)],[c_385]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1717,plain,
% 3.47/0.99      ( r2_hidden(sK0(sK5),sK5) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4,plain,
% 3.47/0.99      ( ~ r2_hidden(X0,X1) | k2_xboole_0(k2_tarski(X0,X0),X1) = X1 ),
% 3.47/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1738,plain,
% 3.47/0.99      ( k2_xboole_0(k2_tarski(X0,X0),X1) = X1
% 3.47/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3006,plain,
% 3.47/0.99      ( k2_xboole_0(k2_tarski(sK0(sK5),sK0(sK5)),sK5) = sK5 ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1717,c_1738]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_5,plain,
% 3.47/0.99      ( k2_xboole_0(k2_tarski(X0,X0),X1) != k1_xboole_0 ),
% 3.47/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4250,plain,
% 3.47/0.99      ( sK5 != k1_xboole_0 ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_3006,c_5]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_30,negated_conjecture,
% 3.47/0.99      ( ~ v1_xboole_0(sK3) ),
% 3.47/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_399,plain,
% 3.47/0.99      ( r2_hidden(sK0(X0),X0) | sK3 != X0 ),
% 3.47/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_30]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_400,plain,
% 3.47/0.99      ( r2_hidden(sK0(sK3),sK3) ),
% 3.47/0.99      inference(unflattening,[status(thm)],[c_399]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1715,plain,
% 3.47/0.99      ( r2_hidden(sK0(sK3),sK3) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3008,plain,
% 3.47/0.99      ( k2_xboole_0(k2_tarski(sK0(sK3),sK0(sK3)),sK3) = sK3 ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1715,c_1738]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4307,plain,
% 3.47/0.99      ( sK3 != k1_xboole_0 ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_3008,c_5]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_9688,plain,
% 3.47/0.99      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.47/0.99      | r2_hidden(sK2(X0,X1,sK6),sK5) = iProver_top ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_9216,c_4250,c_4307]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6,plain,
% 3.47/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1737,plain,
% 3.47/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.47/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_9697,plain,
% 3.47/0.99      ( m1_subset_1(sK2(X0,X1,sK6),sK5) = iProver_top
% 3.47/0.99      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_9688,c_1737]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_25,negated_conjecture,
% 3.47/0.99      ( m1_subset_1(sK8,sK5)
% 3.47/0.99      | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1723,plain,
% 3.47/0.99      ( m1_subset_1(sK8,sK5) = iProver_top
% 3.47/0.99      | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_22,negated_conjecture,
% 3.47/0.99      ( ~ m1_subset_1(X0,sK5)
% 3.47/0.99      | ~ r2_hidden(X0,sK4)
% 3.47/0.99      | ~ r2_hidden(k4_tarski(X0,sK7),sK6)
% 3.47/0.99      | ~ r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1726,plain,
% 3.47/0.99      ( m1_subset_1(X0,sK5) != iProver_top
% 3.47/0.99      | r2_hidden(X0,sK4) != iProver_top
% 3.47/0.99      | r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top
% 3.47/0.99      | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1994,plain,
% 3.47/0.99      ( m1_subset_1(X0,sK5) != iProver_top
% 3.47/0.99      | m1_subset_1(sK8,sK5) = iProver_top
% 3.47/0.99      | r2_hidden(X0,sK4) != iProver_top
% 3.47/0.99      | r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1723,c_1726]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4584,plain,
% 3.47/0.99      ( m1_subset_1(sK2(sK7,X0,sK6),sK5) != iProver_top
% 3.47/0.99      | m1_subset_1(sK8,sK5) = iProver_top
% 3.47/0.99      | r2_hidden(sK2(sK7,X0,sK6),sK4) != iProver_top
% 3.47/0.99      | r2_hidden(sK7,k9_relat_1(sK6,X0)) != iProver_top
% 3.47/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1731,c_1994]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_9788,plain,
% 3.47/0.99      ( m1_subset_1(sK8,sK5) = iProver_top
% 3.47/0.99      | r2_hidden(sK2(sK7,X0,sK6),sK4) != iProver_top
% 3.47/0.99      | r2_hidden(sK7,k9_relat_1(sK6,X0)) != iProver_top
% 3.47/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_9697,c_4584]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_21,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.47/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1727,plain,
% 3.47/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.47/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2729,plain,
% 3.47/0.99      ( k7_relset_1(sK5,sK3,sK6,X0) = k9_relat_1(sK6,X0) ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1721,c_1727]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_24,negated_conjecture,
% 3.47/0.99      ( r2_hidden(k4_tarski(sK8,sK7),sK6)
% 3.47/0.99      | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1724,plain,
% 3.47/0.99      ( r2_hidden(k4_tarski(sK8,sK7),sK6) = iProver_top
% 3.47/0.99      | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3133,plain,
% 3.47/0.99      ( r2_hidden(k4_tarski(sK8,sK7),sK6) = iProver_top
% 3.47/0.99      | r2_hidden(sK7,k9_relat_1(sK6,sK4)) = iProver_top ),
% 3.47/0.99      inference(demodulation,[status(thm)],[c_2729,c_1724]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4312,plain,
% 3.47/0.99      ( k2_xboole_0(k2_tarski(X0,X0),k2_zfmisc_1(sK5,sK3)) = k2_zfmisc_1(sK5,sK3)
% 3.47/0.99      | r2_hidden(X0,sK6) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_3878,c_1738]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_5772,plain,
% 3.47/0.99      ( k2_xboole_0(k2_tarski(k4_tarski(sK8,sK7),k4_tarski(sK8,sK7)),k2_zfmisc_1(sK5,sK3)) = k2_zfmisc_1(sK5,sK3)
% 3.47/0.99      | r2_hidden(sK7,k9_relat_1(sK6,sK4)) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_3133,c_4312]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_23,negated_conjecture,
% 3.47/0.99      ( r2_hidden(sK8,sK4)
% 3.47/0.99      | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1725,plain,
% 3.47/0.99      ( r2_hidden(sK8,sK4) = iProver_top
% 3.47/0.99      | r2_hidden(sK7,k7_relset_1(sK5,sK3,sK6,sK4)) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3134,plain,
% 3.47/0.99      ( r2_hidden(sK8,sK4) = iProver_top
% 3.47/0.99      | r2_hidden(sK7,k9_relat_1(sK6,sK4)) = iProver_top ),
% 3.47/0.99      inference(demodulation,[status(thm)],[c_2729,c_1725]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_11,plain,
% 3.47/0.99      ( ~ r2_hidden(X0,X1)
% 3.47/0.99      | r2_hidden(X2,k9_relat_1(X3,X1))
% 3.47/0.99      | ~ r2_hidden(X0,k1_relat_1(X3))
% 3.47/0.99      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 3.47/0.99      | ~ v1_relat_1(X3) ),
% 3.47/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1733,plain,
% 3.47/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.47/0.99      | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
% 3.47/0.99      | r2_hidden(X0,k1_relat_1(X3)) != iProver_top
% 3.47/0.99      | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
% 3.47/0.99      | v1_relat_1(X3) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1875,plain,
% 3.47/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.47/0.99      | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
% 3.47/0.99      | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
% 3.47/0.99      | v1_relat_1(X3) != iProver_top ),
% 3.47/0.99      inference(forward_subsumption_resolution,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_1733,c_1728]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_5075,plain,
% 3.47/0.99      ( r2_hidden(sK8,X0) != iProver_top
% 3.47/0.99      | r2_hidden(sK7,k9_relat_1(sK6,X0)) = iProver_top
% 3.47/0.99      | r2_hidden(sK7,k9_relat_1(sK6,sK4)) = iProver_top
% 3.47/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_3133,c_1875]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_5676,plain,
% 3.47/0.99      ( r2_hidden(sK8,sK4) != iProver_top
% 3.47/0.99      | r2_hidden(sK7,k9_relat_1(sK6,sK4)) = iProver_top
% 3.47/0.99      | v1_relat_1(sK6) != iProver_top
% 3.47/0.99      | iProver_top != iProver_top ),
% 3.47/0.99      inference(equality_factoring,[status(thm)],[c_5075]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_5678,plain,
% 3.47/0.99      ( r2_hidden(sK8,sK4) != iProver_top
% 3.47/0.99      | r2_hidden(sK7,k9_relat_1(sK6,sK4)) = iProver_top
% 3.47/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.47/0.99      inference(equality_resolution_simp,[status(thm)],[c_5676]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6114,plain,
% 3.47/0.99      ( r2_hidden(sK7,k9_relat_1(sK6,sK4)) = iProver_top ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_5772,c_3134,c_5678,c_6049]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3136,plain,
% 3.47/0.99      ( m1_subset_1(X0,sK5) != iProver_top
% 3.47/0.99      | r2_hidden(X0,sK4) != iProver_top
% 3.47/0.99      | r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top
% 3.47/0.99      | r2_hidden(sK7,k9_relat_1(sK6,sK4)) != iProver_top ),
% 3.47/0.99      inference(demodulation,[status(thm)],[c_2729,c_1726]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4581,plain,
% 3.47/0.99      ( m1_subset_1(sK2(sK7,X0,sK6),sK5) != iProver_top
% 3.47/0.99      | r2_hidden(sK2(sK7,X0,sK6),sK4) != iProver_top
% 3.47/0.99      | r2_hidden(sK7,k9_relat_1(sK6,X0)) != iProver_top
% 3.47/0.99      | r2_hidden(sK7,k9_relat_1(sK6,sK4)) != iProver_top
% 3.47/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1731,c_3136]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_9786,plain,
% 3.47/0.99      ( r2_hidden(sK2(sK7,X0,sK6),sK4) != iProver_top
% 3.47/0.99      | r2_hidden(sK7,k9_relat_1(sK6,X0)) != iProver_top
% 3.47/0.99      | r2_hidden(sK7,k9_relat_1(sK6,sK4)) != iProver_top
% 3.47/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_9697,c_4581]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_9985,plain,
% 3.47/0.99      ( r2_hidden(sK7,k9_relat_1(sK6,X0)) != iProver_top
% 3.47/0.99      | r2_hidden(sK2(sK7,X0,sK6),sK4) != iProver_top ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_9788,c_3134,c_5678,c_6049,c_9786]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_9986,plain,
% 3.47/0.99      ( r2_hidden(sK2(sK7,X0,sK6),sK4) != iProver_top
% 3.47/0.99      | r2_hidden(sK7,k9_relat_1(sK6,X0)) != iProver_top ),
% 3.47/0.99      inference(renaming,[status(thm)],[c_9985]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_9991,plain,
% 3.47/0.99      ( r2_hidden(sK7,k9_relat_1(sK6,sK4)) != iProver_top
% 3.47/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1732,c_9986]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(contradiction,plain,
% 3.47/0.99      ( $false ),
% 3.47/0.99      inference(minisat,[status(thm)],[c_9991,c_6114,c_6049]) ).
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  ------                               Statistics
% 3.47/0.99  
% 3.47/0.99  ------ General
% 3.47/0.99  
% 3.47/0.99  abstr_ref_over_cycles:                  0
% 3.47/0.99  abstr_ref_under_cycles:                 0
% 3.47/0.99  gc_basic_clause_elim:                   0
% 3.47/0.99  forced_gc_time:                         0
% 3.47/0.99  parsing_time:                           0.009
% 3.47/0.99  unif_index_cands_time:                  0.
% 3.47/0.99  unif_index_add_time:                    0.
% 3.47/0.99  orderings_time:                         0.
% 3.47/0.99  out_proof_time:                         0.01
% 3.47/0.99  total_time:                             0.288
% 3.47/0.99  num_of_symbols:                         55
% 3.47/0.99  num_of_terms:                           9286
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing
% 3.47/0.99  
% 3.47/0.99  num_of_splits:                          0
% 3.47/0.99  num_of_split_atoms:                     0
% 3.47/0.99  num_of_reused_defs:                     0
% 3.47/0.99  num_eq_ax_congr_red:                    31
% 3.47/0.99  num_of_sem_filtered_clauses:            1
% 3.47/0.99  num_of_subtypes:                        0
% 3.47/0.99  monotx_restored_types:                  0
% 3.47/0.99  sat_num_of_epr_types:                   0
% 3.47/0.99  sat_num_of_non_cyclic_types:            0
% 3.47/0.99  sat_guarded_non_collapsed_types:        0
% 3.47/0.99  num_pure_diseq_elim:                    0
% 3.47/0.99  simp_replaced_by:                       0
% 3.47/0.99  res_preprocessed:                       150
% 3.47/0.99  prep_upred:                             0
% 3.47/0.99  prep_unflattend:                        37
% 3.47/0.99  smt_new_axioms:                         0
% 3.47/0.99  pred_elim_cands:                        4
% 3.47/0.99  pred_elim:                              1
% 3.47/0.99  pred_elim_cl:                           1
% 3.47/0.99  pred_elim_cycles:                       3
% 3.47/0.99  merged_defs:                            8
% 3.47/0.99  merged_defs_ncl:                        0
% 3.47/0.99  bin_hyper_res:                          9
% 3.47/0.99  prep_cycles:                            4
% 3.47/0.99  pred_elim_time:                         0.009
% 3.47/0.99  splitting_time:                         0.
% 3.47/0.99  sem_filter_time:                        0.
% 3.47/0.99  monotx_time:                            0.
% 3.47/0.99  subtype_inf_time:                       0.
% 3.47/0.99  
% 3.47/0.99  ------ Problem properties
% 3.47/0.99  
% 3.47/0.99  clauses:                                30
% 3.47/0.99  conjectures:                            6
% 3.47/0.99  epr:                                    4
% 3.47/0.99  horn:                                   24
% 3.47/0.99  ground:                                 8
% 3.47/0.99  unary:                                  7
% 3.47/0.99  binary:                                 10
% 3.47/0.99  lits:                                   69
% 3.47/0.99  lits_eq:                                9
% 3.47/0.99  fd_pure:                                0
% 3.47/0.99  fd_pseudo:                              0
% 3.47/0.99  fd_cond:                                0
% 3.47/0.99  fd_pseudo_cond:                         0
% 3.47/0.99  ac_symbols:                             0
% 3.47/0.99  
% 3.47/0.99  ------ Propositional Solver
% 3.47/0.99  
% 3.47/0.99  prop_solver_calls:                      28
% 3.47/0.99  prop_fast_solver_calls:                 1172
% 3.47/0.99  smt_solver_calls:                       0
% 3.47/0.99  smt_fast_solver_calls:                  0
% 3.47/0.99  prop_num_of_clauses:                    3219
% 3.47/0.99  prop_preprocess_simplified:             8604
% 3.47/0.99  prop_fo_subsumed:                       39
% 3.47/0.99  prop_solver_time:                       0.
% 3.47/0.99  smt_solver_time:                        0.
% 3.47/0.99  smt_fast_solver_time:                   0.
% 3.47/0.99  prop_fast_solver_time:                  0.
% 3.47/0.99  prop_unsat_core_time:                   0.
% 3.47/0.99  
% 3.47/0.99  ------ QBF
% 3.47/0.99  
% 3.47/0.99  qbf_q_res:                              0
% 3.47/0.99  qbf_num_tautologies:                    0
% 3.47/0.99  qbf_prep_cycles:                        0
% 3.47/0.99  
% 3.47/0.99  ------ BMC1
% 3.47/0.99  
% 3.47/0.99  bmc1_current_bound:                     -1
% 3.47/0.99  bmc1_last_solved_bound:                 -1
% 3.47/0.99  bmc1_unsat_core_size:                   -1
% 3.47/0.99  bmc1_unsat_core_parents_size:           -1
% 3.47/0.99  bmc1_merge_next_fun:                    0
% 3.47/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.47/0.99  
% 3.47/0.99  ------ Instantiation
% 3.47/0.99  
% 3.47/0.99  inst_num_of_clauses:                    934
% 3.47/0.99  inst_num_in_passive:                    295
% 3.47/0.99  inst_num_in_active:                     466
% 3.47/0.99  inst_num_in_unprocessed:                173
% 3.47/0.99  inst_num_of_loops:                      630
% 3.47/0.99  inst_num_of_learning_restarts:          0
% 3.47/0.99  inst_num_moves_active_passive:          162
% 3.47/0.99  inst_lit_activity:                      0
% 3.47/0.99  inst_lit_activity_moves:                0
% 3.47/0.99  inst_num_tautologies:                   0
% 3.47/0.99  inst_num_prop_implied:                  0
% 3.47/0.99  inst_num_existing_simplified:           0
% 3.47/0.99  inst_num_eq_res_simplified:             0
% 3.47/0.99  inst_num_child_elim:                    0
% 3.47/0.99  inst_num_of_dismatching_blockings:      224
% 3.47/0.99  inst_num_of_non_proper_insts:           808
% 3.47/0.99  inst_num_of_duplicates:                 0
% 3.47/0.99  inst_inst_num_from_inst_to_res:         0
% 3.47/0.99  inst_dismatching_checking_time:         0.
% 3.47/0.99  
% 3.47/0.99  ------ Resolution
% 3.47/0.99  
% 3.47/0.99  res_num_of_clauses:                     0
% 3.47/0.99  res_num_in_passive:                     0
% 3.47/0.99  res_num_in_active:                      0
% 3.47/0.99  res_num_of_loops:                       154
% 3.47/0.99  res_forward_subset_subsumed:            54
% 3.47/0.99  res_backward_subset_subsumed:           0
% 3.47/0.99  res_forward_subsumed:                   0
% 3.47/0.99  res_backward_subsumed:                  0
% 3.47/0.99  res_forward_subsumption_resolution:     0
% 3.47/0.99  res_backward_subsumption_resolution:    0
% 3.47/0.99  res_clause_to_clause_subsumption:       601
% 3.47/0.99  res_orphan_elimination:                 0
% 3.47/0.99  res_tautology_del:                      47
% 3.47/0.99  res_num_eq_res_simplified:              0
% 3.47/0.99  res_num_sel_changes:                    0
% 3.47/0.99  res_moves_from_active_to_pass:          0
% 3.47/0.99  
% 3.47/0.99  ------ Superposition
% 3.47/0.99  
% 3.47/0.99  sup_time_total:                         0.
% 3.47/0.99  sup_time_generating:                    0.
% 3.47/0.99  sup_time_sim_full:                      0.
% 3.47/0.99  sup_time_sim_immed:                     0.
% 3.47/0.99  
% 3.47/0.99  sup_num_of_clauses:                     184
% 3.47/0.99  sup_num_in_active:                      105
% 3.47/0.99  sup_num_in_passive:                     79
% 3.47/0.99  sup_num_of_loops:                       124
% 3.47/0.99  sup_fw_superposition:                   136
% 3.47/0.99  sup_bw_superposition:                   116
% 3.47/0.99  sup_immediate_simplified:               54
% 3.47/0.99  sup_given_eliminated:                   0
% 3.47/0.99  comparisons_done:                       0
% 3.47/0.99  comparisons_avoided:                    6
% 3.47/0.99  
% 3.47/0.99  ------ Simplifications
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  sim_fw_subset_subsumed:                 16
% 3.47/0.99  sim_bw_subset_subsumed:                 22
% 3.47/0.99  sim_fw_subsumed:                        3
% 3.47/0.99  sim_bw_subsumed:                        22
% 3.47/0.99  sim_fw_subsumption_res:                 7
% 3.47/0.99  sim_bw_subsumption_res:                 3
% 3.47/0.99  sim_tautology_del:                      8
% 3.47/0.99  sim_eq_tautology_del:                   0
% 3.47/0.99  sim_eq_res_simp:                        1
% 3.47/0.99  sim_fw_demodulated:                     3
% 3.47/0.99  sim_bw_demodulated:                     13
% 3.47/0.99  sim_light_normalised:                   3
% 3.47/0.99  sim_joinable_taut:                      0
% 3.47/0.99  sim_joinable_simp:                      0
% 3.47/0.99  sim_ac_normalised:                      0
% 3.47/0.99  sim_smt_subsumption:                    0
% 3.47/0.99  
%------------------------------------------------------------------------------

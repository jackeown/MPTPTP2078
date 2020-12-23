%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:06 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 764 expanded)
%              Number of clauses        :   67 ( 212 expanded)
%              Number of leaves         :   19 ( 251 expanded)
%              Depth                    :   22
%              Number of atoms          :  550 (6607 expanded)
%              Number of equality atoms :  147 ( 397 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f26])).

fof(f30,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK1(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30,f29,f28])).

fof(f55,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f54,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X4,X5),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <~> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X4,X5),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                      & ( ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) )
                        | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X4,X5),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                      & ( ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) )
                        | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X4,X5),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                      & ( ? [X6] :
                            ( r2_hidden(X6,X1)
                            & r2_hidden(k4_tarski(X4,X6),X3)
                            & m1_subset_1(X6,X2) )
                        | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(rectify,[],[f37])).

fof(f44,plain,(
    ! [X4,X2,X3,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X4,X6),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK9,X1)
        & r2_hidden(k4_tarski(X4,sK9),X3)
        & m1_subset_1(sK9,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,X1)
                & r2_hidden(k4_tarski(X4,X6),X3)
                & m1_subset_1(X6,X2) )
            | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & m1_subset_1(X4,X0) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(X5,X1)
              | ~ r2_hidden(k4_tarski(sK8,X5),X3)
              | ~ m1_subset_1(X5,X2) )
          | ~ r2_hidden(sK8,k8_relset_1(X0,X2,X3,X1)) )
        & ( ? [X6] :
              ( r2_hidden(X6,X1)
              & r2_hidden(k4_tarski(sK8,X6),X3)
              & m1_subset_1(X6,X2) )
          | r2_hidden(sK8,k8_relset_1(X0,X2,X3,X1)) )
        & m1_subset_1(sK8,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ! [X5] :
                    ( ~ r2_hidden(X5,X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X3)
                    | ~ m1_subset_1(X5,X2) )
                | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
              & ( ? [X6] :
                    ( r2_hidden(X6,X1)
                    & r2_hidden(k4_tarski(X4,X6),X3)
                    & m1_subset_1(X6,X2) )
                | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
              & m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
     => ( ? [X4] :
            ( ( ! [X5] :
                  ( ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(k4_tarski(X4,X5),sK7)
                  | ~ m1_subset_1(X5,X2) )
              | ~ r2_hidden(X4,k8_relset_1(X0,X2,sK7,X1)) )
            & ( ? [X6] :
                  ( r2_hidden(X6,X1)
                  & r2_hidden(k4_tarski(X4,X6),sK7)
                  & m1_subset_1(X6,X2) )
              | r2_hidden(X4,k8_relset_1(X0,X2,sK7,X1)) )
            & m1_subset_1(X4,X0) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ! [X5] :
                        ( ~ r2_hidden(X5,X1)
                        | ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ m1_subset_1(X5,X2) )
                    | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                  & ( ? [X6] :
                        ( r2_hidden(X6,X1)
                        & r2_hidden(k4_tarski(X4,X6),X3)
                        & m1_subset_1(X6,X2) )
                    | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
          & ~ v1_xboole_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ( ! [X5] :
                      ( ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(k4_tarski(X4,X5),X3)
                      | ~ m1_subset_1(X5,sK6) )
                  | ~ r2_hidden(X4,k8_relset_1(X0,sK6,X3,X1)) )
                & ( ? [X6] :
                      ( r2_hidden(X6,X1)
                      & r2_hidden(k4_tarski(X4,X6),X3)
                      & m1_subset_1(X6,sK6) )
                  | r2_hidden(X4,k8_relset_1(X0,sK6,X3,X1)) )
                & m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,sK6))) )
        & ~ v1_xboole_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X4,X5),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                      & ( ? [X6] :
                            ( r2_hidden(X6,X1)
                            & r2_hidden(k4_tarski(X4,X6),X3)
                            & m1_subset_1(X6,X2) )
                        | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ! [X5] :
                          ( ~ r2_hidden(X5,sK5)
                          | ~ r2_hidden(k4_tarski(X4,X5),X3)
                          | ~ m1_subset_1(X5,X2) )
                      | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,sK5)) )
                    & ( ? [X6] :
                          ( r2_hidden(X6,sK5)
                          & r2_hidden(k4_tarski(X4,X6),X3)
                          & m1_subset_1(X6,X2) )
                      | r2_hidden(X4,k8_relset_1(X0,X2,X3,sK5)) )
                    & m1_subset_1(X4,X0) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X4,X5),X3)
                              | ~ m1_subset_1(X5,X2) )
                          | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                        & ( ? [X6] :
                              ( r2_hidden(X6,X1)
                              & r2_hidden(k4_tarski(X4,X6),X3)
                              & m1_subset_1(X6,X2) )
                          | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
                        & m1_subset_1(X4,X0) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
                & ~ v1_xboole_0(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X4,X5),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k8_relset_1(sK4,X2,X3,X1)) )
                      & ( ? [X6] :
                            ( r2_hidden(X6,X1)
                            & r2_hidden(k4_tarski(X4,X6),X3)
                            & m1_subset_1(X6,X2) )
                        | r2_hidden(X4,k8_relset_1(sK4,X2,X3,X1)) )
                      & m1_subset_1(X4,sK4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,X2))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ! [X5] :
          ( ~ r2_hidden(X5,sK5)
          | ~ r2_hidden(k4_tarski(sK8,X5),sK7)
          | ~ m1_subset_1(X5,sK6) )
      | ~ r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) )
    & ( ( r2_hidden(sK9,sK5)
        & r2_hidden(k4_tarski(sK8,sK9),sK7)
        & m1_subset_1(sK9,sK6) )
      | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) )
    & m1_subset_1(sK8,sK4)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    & ~ v1_xboole_0(sK6)
    & ~ v1_xboole_0(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f38,f44,f43,f42,f41,f40,f39])).

fof(f69,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,
    ( m1_subset_1(sK9,sK6)
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK5)
      | ~ r2_hidden(k4_tarski(sK8,X5),sK7)
      | ~ m1_subset_1(X5,sK6)
      | ~ r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK7)
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,
    ( r2_hidden(sK9,sK5)
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
    inference(cnf_transformation,[],[f45])).

fof(f56,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1111,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK2(X1,X2,X0),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK2(X1,X2,X0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1110,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(X1,X2,X0)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1099,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1118,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2440,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(sK4,sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1099,c_1118])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1119,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2655,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK4,sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2440,c_1119])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1117,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2432,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1099,c_1117])).

cnf(c_4128,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X0,k2_zfmisc_1(sK4,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2655,c_2432])).

cnf(c_4129,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK4,sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_4128])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1122,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4137,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4129,c_1122])).

cnf(c_4477,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK2(sK7,X1,X0),sK6) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1110,c_4137])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1116,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2158,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK6)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1099,c_1116])).

cnf(c_14,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1109,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2253,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2158,c_1109])).

cnf(c_5324,plain,
    ( r2_hidden(sK2(sK7,X1,X0),sK6) = iProver_top
    | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4477,c_2253])).

cnf(c_5325,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK2(sK7,X1,X0),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_5324])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1120,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5332,plain,
    ( m1_subset_1(sK2(sK7,X0,X1),sK6) = iProver_top
    | r2_hidden(X1,k10_relat_1(sK7,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5325,c_1120])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK9,sK6)
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1101,plain,
    ( m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,negated_conjecture,
    ( ~ m1_subset_1(X0,sK6)
    | ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(k4_tarski(sK8,X0),sK7)
    | ~ r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1104,plain,
    ( m1_subset_1(X0,sK6) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(sK8,X0),sK7) != iProver_top
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1446,plain,
    ( m1_subset_1(X0,sK6) != iProver_top
    | m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(sK8,X0),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1101,c_1104])).

cnf(c_3289,plain,
    ( m1_subset_1(sK2(sK7,X0,sK8),sK6) != iProver_top
    | m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1110,c_1446])).

cnf(c_3479,plain,
    ( r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
    | m1_subset_1(sK9,sK6) = iProver_top
    | m1_subset_1(sK2(sK7,X0,sK8),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3289,c_2253])).

cnf(c_3480,plain,
    ( m1_subset_1(sK2(sK7,X0,sK8),sK6) != iProver_top
    | m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3479])).

cnf(c_5639,plain,
    ( m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5332,c_3480])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1105,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2357,plain,
    ( k8_relset_1(sK4,sK6,sK7,X0) = k10_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_1099,c_1105])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(k4_tarski(sK8,sK9),sK7)
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1102,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK7) = iProver_top
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2581,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK7) = iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2357,c_1102])).

cnf(c_4479,plain,
    ( r2_hidden(sK9,sK6) = iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2581,c_4137])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK9,sK5)
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1103,plain,
    ( r2_hidden(sK9,sK5) = iProver_top
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2582,plain,
    ( r2_hidden(sK9,sK5) = iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2357,c_1103])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1112,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3731,plain,
    ( r2_hidden(sK9,X0) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) = iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2581,c_1112])).

cnf(c_4180,plain,
    ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) = iProver_top
    | r2_hidden(sK9,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3731,c_2253])).

cnf(c_4181,plain,
    ( r2_hidden(sK9,X0) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) = iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4180])).

cnf(c_4191,plain,
    ( r2_hidden(sK9,sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_4181])).

cnf(c_4193,plain,
    ( r2_hidden(sK9,sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4191])).

cnf(c_4509,plain,
    ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4479,c_2582,c_4193])).

cnf(c_2584,plain,
    ( m1_subset_1(X0,sK6) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(sK8,X0),sK7) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2357,c_1104])).

cnf(c_3286,plain,
    ( m1_subset_1(sK2(sK7,X0,sK8),sK6) != iProver_top
    | r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1110,c_2584])).

cnf(c_4039,plain,
    ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
    | m1_subset_1(sK2(sK7,X0,sK8),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3286,c_2253])).

cnf(c_4040,plain,
    ( m1_subset_1(sK2(sK7,X0,sK8),sK6) != iProver_top
    | r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4039])).

cnf(c_5637,plain,
    ( r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5332,c_4040])).

cnf(c_6020,plain,
    ( r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5639,c_2582,c_4193,c_5637])).

cnf(c_6028,plain,
    ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1111,c_6020])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6028,c_4509,c_2253])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:31:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.98/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/0.98  
% 2.98/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.98/0.98  
% 2.98/0.98  ------  iProver source info
% 2.98/0.98  
% 2.98/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.98/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.98/0.98  git: non_committed_changes: false
% 2.98/0.98  git: last_make_outside_of_git: false
% 2.98/0.98  
% 2.98/0.98  ------ 
% 2.98/0.98  
% 2.98/0.98  ------ Input Options
% 2.98/0.98  
% 2.98/0.98  --out_options                           all
% 2.98/0.98  --tptp_safe_out                         true
% 2.98/0.98  --problem_path                          ""
% 2.98/0.98  --include_path                          ""
% 2.98/0.98  --clausifier                            res/vclausify_rel
% 2.98/0.98  --clausifier_options                    --mode clausify
% 2.98/0.98  --stdin                                 false
% 2.98/0.98  --stats_out                             all
% 2.98/0.98  
% 2.98/0.98  ------ General Options
% 2.98/0.98  
% 2.98/0.98  --fof                                   false
% 2.98/0.98  --time_out_real                         305.
% 2.98/0.98  --time_out_virtual                      -1.
% 2.98/0.98  --symbol_type_check                     false
% 2.98/0.98  --clausify_out                          false
% 2.98/0.98  --sig_cnt_out                           false
% 2.98/0.98  --trig_cnt_out                          false
% 2.98/0.98  --trig_cnt_out_tolerance                1.
% 2.98/0.98  --trig_cnt_out_sk_spl                   false
% 2.98/0.98  --abstr_cl_out                          false
% 2.98/0.98  
% 2.98/0.98  ------ Global Options
% 2.98/0.98  
% 2.98/0.98  --schedule                              default
% 2.98/0.98  --add_important_lit                     false
% 2.98/0.98  --prop_solver_per_cl                    1000
% 2.98/0.98  --min_unsat_core                        false
% 2.98/0.98  --soft_assumptions                      false
% 2.98/0.98  --soft_lemma_size                       3
% 2.98/0.98  --prop_impl_unit_size                   0
% 2.98/0.98  --prop_impl_unit                        []
% 2.98/0.98  --share_sel_clauses                     true
% 2.98/0.98  --reset_solvers                         false
% 2.98/0.98  --bc_imp_inh                            [conj_cone]
% 2.98/0.98  --conj_cone_tolerance                   3.
% 2.98/0.98  --extra_neg_conj                        none
% 2.98/0.98  --large_theory_mode                     true
% 2.98/0.98  --prolific_symb_bound                   200
% 2.98/0.98  --lt_threshold                          2000
% 2.98/0.98  --clause_weak_htbl                      true
% 2.98/0.98  --gc_record_bc_elim                     false
% 2.98/0.98  
% 2.98/0.98  ------ Preprocessing Options
% 2.98/0.98  
% 2.98/0.98  --preprocessing_flag                    true
% 2.98/0.98  --time_out_prep_mult                    0.1
% 2.98/0.98  --splitting_mode                        input
% 2.98/0.98  --splitting_grd                         true
% 2.98/0.98  --splitting_cvd                         false
% 2.98/0.98  --splitting_cvd_svl                     false
% 2.98/0.98  --splitting_nvd                         32
% 2.98/0.98  --sub_typing                            true
% 2.98/0.98  --prep_gs_sim                           true
% 2.98/0.98  --prep_unflatten                        true
% 2.98/0.98  --prep_res_sim                          true
% 2.98/0.98  --prep_upred                            true
% 2.98/0.98  --prep_sem_filter                       exhaustive
% 2.98/0.98  --prep_sem_filter_out                   false
% 2.98/0.98  --pred_elim                             true
% 2.98/0.98  --res_sim_input                         true
% 2.98/0.98  --eq_ax_congr_red                       true
% 2.98/0.98  --pure_diseq_elim                       true
% 2.98/0.98  --brand_transform                       false
% 2.98/0.98  --non_eq_to_eq                          false
% 2.98/0.98  --prep_def_merge                        true
% 2.98/0.98  --prep_def_merge_prop_impl              false
% 2.98/0.98  --prep_def_merge_mbd                    true
% 2.98/0.98  --prep_def_merge_tr_red                 false
% 2.98/0.98  --prep_def_merge_tr_cl                  false
% 2.98/0.98  --smt_preprocessing                     true
% 2.98/0.98  --smt_ac_axioms                         fast
% 2.98/0.98  --preprocessed_out                      false
% 2.98/0.98  --preprocessed_stats                    false
% 2.98/0.98  
% 2.98/0.98  ------ Abstraction refinement Options
% 2.98/0.98  
% 2.98/0.98  --abstr_ref                             []
% 2.98/0.98  --abstr_ref_prep                        false
% 2.98/0.98  --abstr_ref_until_sat                   false
% 2.98/0.98  --abstr_ref_sig_restrict                funpre
% 2.98/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/0.98  --abstr_ref_under                       []
% 2.98/0.98  
% 2.98/0.98  ------ SAT Options
% 2.98/0.98  
% 2.98/0.98  --sat_mode                              false
% 2.98/0.98  --sat_fm_restart_options                ""
% 2.98/0.98  --sat_gr_def                            false
% 2.98/0.98  --sat_epr_types                         true
% 2.98/0.98  --sat_non_cyclic_types                  false
% 2.98/0.98  --sat_finite_models                     false
% 2.98/0.98  --sat_fm_lemmas                         false
% 2.98/0.98  --sat_fm_prep                           false
% 2.98/0.98  --sat_fm_uc_incr                        true
% 2.98/0.98  --sat_out_model                         small
% 2.98/0.98  --sat_out_clauses                       false
% 2.98/0.98  
% 2.98/0.98  ------ QBF Options
% 2.98/0.98  
% 2.98/0.98  --qbf_mode                              false
% 2.98/0.98  --qbf_elim_univ                         false
% 2.98/0.98  --qbf_dom_inst                          none
% 2.98/0.98  --qbf_dom_pre_inst                      false
% 2.98/0.98  --qbf_sk_in                             false
% 2.98/0.98  --qbf_pred_elim                         true
% 2.98/0.98  --qbf_split                             512
% 2.98/0.98  
% 2.98/0.98  ------ BMC1 Options
% 2.98/0.98  
% 2.98/0.98  --bmc1_incremental                      false
% 2.98/0.98  --bmc1_axioms                           reachable_all
% 2.98/0.98  --bmc1_min_bound                        0
% 2.98/0.98  --bmc1_max_bound                        -1
% 2.98/0.98  --bmc1_max_bound_default                -1
% 2.98/0.98  --bmc1_symbol_reachability              true
% 2.98/0.98  --bmc1_property_lemmas                  false
% 2.98/0.98  --bmc1_k_induction                      false
% 2.98/0.98  --bmc1_non_equiv_states                 false
% 2.98/0.98  --bmc1_deadlock                         false
% 2.98/0.98  --bmc1_ucm                              false
% 2.98/0.98  --bmc1_add_unsat_core                   none
% 2.98/0.98  --bmc1_unsat_core_children              false
% 2.98/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/0.98  --bmc1_out_stat                         full
% 2.98/0.98  --bmc1_ground_init                      false
% 2.98/0.98  --bmc1_pre_inst_next_state              false
% 2.98/0.98  --bmc1_pre_inst_state                   false
% 2.98/0.98  --bmc1_pre_inst_reach_state             false
% 2.98/0.98  --bmc1_out_unsat_core                   false
% 2.98/0.98  --bmc1_aig_witness_out                  false
% 2.98/0.98  --bmc1_verbose                          false
% 2.98/0.98  --bmc1_dump_clauses_tptp                false
% 2.98/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.98/0.98  --bmc1_dump_file                        -
% 2.98/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.98/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.98/0.98  --bmc1_ucm_extend_mode                  1
% 2.98/0.98  --bmc1_ucm_init_mode                    2
% 2.98/0.98  --bmc1_ucm_cone_mode                    none
% 2.98/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.98/0.98  --bmc1_ucm_relax_model                  4
% 2.98/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.98/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/0.98  --bmc1_ucm_layered_model                none
% 2.98/0.98  --bmc1_ucm_max_lemma_size               10
% 2.98/0.98  
% 2.98/0.98  ------ AIG Options
% 2.98/0.98  
% 2.98/0.98  --aig_mode                              false
% 2.98/0.98  
% 2.98/0.98  ------ Instantiation Options
% 2.98/0.98  
% 2.98/0.98  --instantiation_flag                    true
% 2.98/0.98  --inst_sos_flag                         false
% 2.98/0.98  --inst_sos_phase                        true
% 2.98/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/0.98  --inst_lit_sel_side                     num_symb
% 2.98/0.98  --inst_solver_per_active                1400
% 2.98/0.98  --inst_solver_calls_frac                1.
% 2.98/0.98  --inst_passive_queue_type               priority_queues
% 2.98/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/0.98  --inst_passive_queues_freq              [25;2]
% 2.98/0.98  --inst_dismatching                      true
% 2.98/0.98  --inst_eager_unprocessed_to_passive     true
% 2.98/0.98  --inst_prop_sim_given                   true
% 2.98/0.98  --inst_prop_sim_new                     false
% 2.98/0.98  --inst_subs_new                         false
% 2.98/0.98  --inst_eq_res_simp                      false
% 2.98/0.98  --inst_subs_given                       false
% 2.98/0.98  --inst_orphan_elimination               true
% 2.98/0.98  --inst_learning_loop_flag               true
% 2.98/0.98  --inst_learning_start                   3000
% 2.98/0.98  --inst_learning_factor                  2
% 2.98/0.98  --inst_start_prop_sim_after_learn       3
% 2.98/0.98  --inst_sel_renew                        solver
% 2.98/0.98  --inst_lit_activity_flag                true
% 2.98/0.98  --inst_restr_to_given                   false
% 2.98/0.98  --inst_activity_threshold               500
% 2.98/0.98  --inst_out_proof                        true
% 2.98/0.98  
% 2.98/0.98  ------ Resolution Options
% 2.98/0.98  
% 2.98/0.98  --resolution_flag                       true
% 2.98/0.98  --res_lit_sel                           adaptive
% 2.98/0.98  --res_lit_sel_side                      none
% 2.98/0.98  --res_ordering                          kbo
% 2.98/0.98  --res_to_prop_solver                    active
% 2.98/0.98  --res_prop_simpl_new                    false
% 2.98/0.98  --res_prop_simpl_given                  true
% 2.98/0.98  --res_passive_queue_type                priority_queues
% 2.98/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/0.98  --res_passive_queues_freq               [15;5]
% 2.98/0.98  --res_forward_subs                      full
% 2.98/0.98  --res_backward_subs                     full
% 2.98/0.98  --res_forward_subs_resolution           true
% 2.98/0.98  --res_backward_subs_resolution          true
% 2.98/0.98  --res_orphan_elimination                true
% 2.98/0.98  --res_time_limit                        2.
% 2.98/0.98  --res_out_proof                         true
% 2.98/0.98  
% 2.98/0.98  ------ Superposition Options
% 2.98/0.98  
% 2.98/0.98  --superposition_flag                    true
% 2.98/0.98  --sup_passive_queue_type                priority_queues
% 2.98/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.98/0.98  --demod_completeness_check              fast
% 2.98/0.98  --demod_use_ground                      true
% 2.98/0.98  --sup_to_prop_solver                    passive
% 2.98/0.98  --sup_prop_simpl_new                    true
% 2.98/0.98  --sup_prop_simpl_given                  true
% 2.98/0.98  --sup_fun_splitting                     false
% 2.98/0.98  --sup_smt_interval                      50000
% 2.98/0.98  
% 2.98/0.98  ------ Superposition Simplification Setup
% 2.98/0.98  
% 2.98/0.98  --sup_indices_passive                   []
% 2.98/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.98  --sup_full_bw                           [BwDemod]
% 2.98/0.98  --sup_immed_triv                        [TrivRules]
% 2.98/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.98  --sup_immed_bw_main                     []
% 2.98/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.98  
% 2.98/0.98  ------ Combination Options
% 2.98/0.98  
% 2.98/0.98  --comb_res_mult                         3
% 2.98/0.98  --comb_sup_mult                         2
% 2.98/0.98  --comb_inst_mult                        10
% 2.98/0.98  
% 2.98/0.98  ------ Debug Options
% 2.98/0.98  
% 2.98/0.98  --dbg_backtrace                         false
% 2.98/0.98  --dbg_dump_prop_clauses                 false
% 2.98/0.98  --dbg_dump_prop_clauses_file            -
% 2.98/0.98  --dbg_out_stat                          false
% 2.98/0.98  ------ Parsing...
% 2.98/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.98/0.98  
% 2.98/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.98/0.98  
% 2.98/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.98/0.98  
% 2.98/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.98/0.98  ------ Proving...
% 2.98/0.98  ------ Problem Properties 
% 2.98/0.98  
% 2.98/0.98  
% 2.98/0.98  clauses                                 28
% 2.98/0.98  conjectures                             9
% 2.98/0.98  EPR                                     6
% 2.98/0.98  Horn                                    22
% 2.98/0.98  unary                                   6
% 2.98/0.98  binary                                  7
% 2.98/0.98  lits                                    71
% 2.98/0.98  lits eq                                 4
% 2.98/0.98  fd_pure                                 0
% 2.98/0.98  fd_pseudo                               0
% 2.98/0.98  fd_cond                                 0
% 2.98/0.98  fd_pseudo_cond                          3
% 2.98/0.98  AC symbols                              0
% 2.98/0.98  
% 2.98/0.98  ------ Schedule dynamic 5 is on 
% 2.98/0.98  
% 2.98/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.98/0.98  
% 2.98/0.98  
% 2.98/0.98  ------ 
% 2.98/0.98  Current options:
% 2.98/0.98  ------ 
% 2.98/0.98  
% 2.98/0.98  ------ Input Options
% 2.98/0.98  
% 2.98/0.98  --out_options                           all
% 2.98/0.98  --tptp_safe_out                         true
% 2.98/0.98  --problem_path                          ""
% 2.98/0.98  --include_path                          ""
% 2.98/0.98  --clausifier                            res/vclausify_rel
% 2.98/0.98  --clausifier_options                    --mode clausify
% 2.98/0.98  --stdin                                 false
% 2.98/0.98  --stats_out                             all
% 2.98/0.98  
% 2.98/0.98  ------ General Options
% 2.98/0.98  
% 2.98/0.98  --fof                                   false
% 2.98/0.98  --time_out_real                         305.
% 2.98/0.98  --time_out_virtual                      -1.
% 2.98/0.98  --symbol_type_check                     false
% 2.98/0.98  --clausify_out                          false
% 2.98/0.98  --sig_cnt_out                           false
% 2.98/0.98  --trig_cnt_out                          false
% 2.98/0.98  --trig_cnt_out_tolerance                1.
% 2.98/0.98  --trig_cnt_out_sk_spl                   false
% 2.98/0.98  --abstr_cl_out                          false
% 2.98/0.98  
% 2.98/0.98  ------ Global Options
% 2.98/0.98  
% 2.98/0.98  --schedule                              default
% 2.98/0.98  --add_important_lit                     false
% 2.98/0.98  --prop_solver_per_cl                    1000
% 2.98/0.98  --min_unsat_core                        false
% 2.98/0.98  --soft_assumptions                      false
% 2.98/0.98  --soft_lemma_size                       3
% 2.98/0.98  --prop_impl_unit_size                   0
% 2.98/0.98  --prop_impl_unit                        []
% 2.98/0.98  --share_sel_clauses                     true
% 2.98/0.98  --reset_solvers                         false
% 2.98/0.98  --bc_imp_inh                            [conj_cone]
% 2.98/0.98  --conj_cone_tolerance                   3.
% 2.98/0.98  --extra_neg_conj                        none
% 2.98/0.98  --large_theory_mode                     true
% 2.98/0.98  --prolific_symb_bound                   200
% 2.98/0.98  --lt_threshold                          2000
% 2.98/0.98  --clause_weak_htbl                      true
% 2.98/0.98  --gc_record_bc_elim                     false
% 2.98/0.98  
% 2.98/0.98  ------ Preprocessing Options
% 2.98/0.98  
% 2.98/0.98  --preprocessing_flag                    true
% 2.98/0.98  --time_out_prep_mult                    0.1
% 2.98/0.98  --splitting_mode                        input
% 2.98/0.98  --splitting_grd                         true
% 2.98/0.98  --splitting_cvd                         false
% 2.98/0.98  --splitting_cvd_svl                     false
% 2.98/0.98  --splitting_nvd                         32
% 2.98/0.98  --sub_typing                            true
% 2.98/0.98  --prep_gs_sim                           true
% 2.98/0.98  --prep_unflatten                        true
% 2.98/0.98  --prep_res_sim                          true
% 2.98/0.98  --prep_upred                            true
% 2.98/0.98  --prep_sem_filter                       exhaustive
% 2.98/0.98  --prep_sem_filter_out                   false
% 2.98/0.98  --pred_elim                             true
% 2.98/0.98  --res_sim_input                         true
% 2.98/0.98  --eq_ax_congr_red                       true
% 2.98/0.98  --pure_diseq_elim                       true
% 2.98/0.98  --brand_transform                       false
% 2.98/0.98  --non_eq_to_eq                          false
% 2.98/0.98  --prep_def_merge                        true
% 2.98/0.98  --prep_def_merge_prop_impl              false
% 2.98/0.98  --prep_def_merge_mbd                    true
% 2.98/0.98  --prep_def_merge_tr_red                 false
% 2.98/0.98  --prep_def_merge_tr_cl                  false
% 2.98/0.98  --smt_preprocessing                     true
% 2.98/0.98  --smt_ac_axioms                         fast
% 2.98/0.98  --preprocessed_out                      false
% 2.98/0.98  --preprocessed_stats                    false
% 2.98/0.98  
% 2.98/0.98  ------ Abstraction refinement Options
% 2.98/0.98  
% 2.98/0.98  --abstr_ref                             []
% 2.98/0.98  --abstr_ref_prep                        false
% 2.98/0.98  --abstr_ref_until_sat                   false
% 2.98/0.98  --abstr_ref_sig_restrict                funpre
% 2.98/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/0.98  --abstr_ref_under                       []
% 2.98/0.98  
% 2.98/0.98  ------ SAT Options
% 2.98/0.98  
% 2.98/0.98  --sat_mode                              false
% 2.98/0.98  --sat_fm_restart_options                ""
% 2.98/0.98  --sat_gr_def                            false
% 2.98/0.98  --sat_epr_types                         true
% 2.98/0.98  --sat_non_cyclic_types                  false
% 2.98/0.98  --sat_finite_models                     false
% 2.98/0.98  --sat_fm_lemmas                         false
% 2.98/0.98  --sat_fm_prep                           false
% 2.98/0.98  --sat_fm_uc_incr                        true
% 2.98/0.98  --sat_out_model                         small
% 2.98/0.98  --sat_out_clauses                       false
% 2.98/0.98  
% 2.98/0.98  ------ QBF Options
% 2.98/0.98  
% 2.98/0.98  --qbf_mode                              false
% 2.98/0.98  --qbf_elim_univ                         false
% 2.98/0.98  --qbf_dom_inst                          none
% 2.98/0.98  --qbf_dom_pre_inst                      false
% 2.98/0.98  --qbf_sk_in                             false
% 2.98/0.98  --qbf_pred_elim                         true
% 2.98/0.98  --qbf_split                             512
% 2.98/0.98  
% 2.98/0.98  ------ BMC1 Options
% 2.98/0.98  
% 2.98/0.98  --bmc1_incremental                      false
% 2.98/0.98  --bmc1_axioms                           reachable_all
% 2.98/0.98  --bmc1_min_bound                        0
% 2.98/0.98  --bmc1_max_bound                        -1
% 2.98/0.98  --bmc1_max_bound_default                -1
% 2.98/0.98  --bmc1_symbol_reachability              true
% 2.98/0.98  --bmc1_property_lemmas                  false
% 2.98/0.98  --bmc1_k_induction                      false
% 2.98/0.98  --bmc1_non_equiv_states                 false
% 2.98/0.98  --bmc1_deadlock                         false
% 2.98/0.98  --bmc1_ucm                              false
% 2.98/0.98  --bmc1_add_unsat_core                   none
% 2.98/0.98  --bmc1_unsat_core_children              false
% 2.98/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/0.98  --bmc1_out_stat                         full
% 2.98/0.98  --bmc1_ground_init                      false
% 2.98/0.98  --bmc1_pre_inst_next_state              false
% 2.98/0.98  --bmc1_pre_inst_state                   false
% 2.98/0.98  --bmc1_pre_inst_reach_state             false
% 2.98/0.98  --bmc1_out_unsat_core                   false
% 2.98/0.98  --bmc1_aig_witness_out                  false
% 2.98/0.98  --bmc1_verbose                          false
% 2.98/0.98  --bmc1_dump_clauses_tptp                false
% 2.98/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.98/0.98  --bmc1_dump_file                        -
% 2.98/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.98/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.98/0.98  --bmc1_ucm_extend_mode                  1
% 2.98/0.98  --bmc1_ucm_init_mode                    2
% 2.98/0.98  --bmc1_ucm_cone_mode                    none
% 2.98/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.98/0.98  --bmc1_ucm_relax_model                  4
% 2.98/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.98/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/0.98  --bmc1_ucm_layered_model                none
% 2.98/0.98  --bmc1_ucm_max_lemma_size               10
% 2.98/0.98  
% 2.98/0.98  ------ AIG Options
% 2.98/0.98  
% 2.98/0.98  --aig_mode                              false
% 2.98/0.98  
% 2.98/0.98  ------ Instantiation Options
% 2.98/0.98  
% 2.98/0.98  --instantiation_flag                    true
% 2.98/0.98  --inst_sos_flag                         false
% 2.98/0.98  --inst_sos_phase                        true
% 2.98/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/0.98  --inst_lit_sel_side                     none
% 2.98/0.98  --inst_solver_per_active                1400
% 2.98/0.98  --inst_solver_calls_frac                1.
% 2.98/0.98  --inst_passive_queue_type               priority_queues
% 2.98/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/0.98  --inst_passive_queues_freq              [25;2]
% 2.98/0.98  --inst_dismatching                      true
% 2.98/0.98  --inst_eager_unprocessed_to_passive     true
% 2.98/0.98  --inst_prop_sim_given                   true
% 2.98/0.98  --inst_prop_sim_new                     false
% 2.98/0.98  --inst_subs_new                         false
% 2.98/0.98  --inst_eq_res_simp                      false
% 2.98/0.98  --inst_subs_given                       false
% 2.98/0.98  --inst_orphan_elimination               true
% 2.98/0.98  --inst_learning_loop_flag               true
% 2.98/0.98  --inst_learning_start                   3000
% 2.98/0.98  --inst_learning_factor                  2
% 2.98/0.98  --inst_start_prop_sim_after_learn       3
% 2.98/0.98  --inst_sel_renew                        solver
% 2.98/0.98  --inst_lit_activity_flag                true
% 2.98/0.98  --inst_restr_to_given                   false
% 2.98/0.98  --inst_activity_threshold               500
% 2.98/0.98  --inst_out_proof                        true
% 2.98/0.98  
% 2.98/0.98  ------ Resolution Options
% 2.98/0.98  
% 2.98/0.98  --resolution_flag                       false
% 2.98/0.98  --res_lit_sel                           adaptive
% 2.98/0.98  --res_lit_sel_side                      none
% 2.98/0.98  --res_ordering                          kbo
% 2.98/0.98  --res_to_prop_solver                    active
% 2.98/0.98  --res_prop_simpl_new                    false
% 2.98/0.98  --res_prop_simpl_given                  true
% 2.98/0.98  --res_passive_queue_type                priority_queues
% 2.98/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/0.98  --res_passive_queues_freq               [15;5]
% 2.98/0.98  --res_forward_subs                      full
% 2.98/0.98  --res_backward_subs                     full
% 2.98/0.98  --res_forward_subs_resolution           true
% 2.98/0.98  --res_backward_subs_resolution          true
% 2.98/0.98  --res_orphan_elimination                true
% 2.98/0.98  --res_time_limit                        2.
% 2.98/0.98  --res_out_proof                         true
% 2.98/0.98  
% 2.98/0.98  ------ Superposition Options
% 2.98/0.98  
% 2.98/0.98  --superposition_flag                    true
% 2.98/0.98  --sup_passive_queue_type                priority_queues
% 2.98/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.98/0.98  --demod_completeness_check              fast
% 2.98/0.98  --demod_use_ground                      true
% 2.98/0.98  --sup_to_prop_solver                    passive
% 2.98/0.98  --sup_prop_simpl_new                    true
% 2.98/0.98  --sup_prop_simpl_given                  true
% 2.98/0.98  --sup_fun_splitting                     false
% 2.98/0.98  --sup_smt_interval                      50000
% 2.98/0.98  
% 2.98/0.98  ------ Superposition Simplification Setup
% 2.98/0.98  
% 2.98/0.98  --sup_indices_passive                   []
% 2.98/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.98  --sup_full_bw                           [BwDemod]
% 2.98/0.98  --sup_immed_triv                        [TrivRules]
% 2.98/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.98  --sup_immed_bw_main                     []
% 2.98/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.98  
% 2.98/0.98  ------ Combination Options
% 2.98/0.98  
% 2.98/0.98  --comb_res_mult                         3
% 2.98/0.98  --comb_sup_mult                         2
% 2.98/0.98  --comb_inst_mult                        10
% 2.98/0.98  
% 2.98/0.98  ------ Debug Options
% 2.98/0.98  
% 2.98/0.98  --dbg_backtrace                         false
% 2.98/0.98  --dbg_dump_prop_clauses                 false
% 2.98/0.98  --dbg_dump_prop_clauses_file            -
% 2.98/0.98  --dbg_out_stat                          false
% 2.98/0.98  
% 2.98/0.98  
% 2.98/0.98  
% 2.98/0.98  
% 2.98/0.98  ------ Proving...
% 2.98/0.98  
% 2.98/0.98  
% 2.98/0.98  % SZS status Theorem for theBenchmark.p
% 2.98/0.98  
% 2.98/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.98/0.98  
% 2.98/0.98  fof(f7,axiom,(
% 2.98/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 2.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f20,plain,(
% 2.98/0.98    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 2.98/0.98    inference(ennf_transformation,[],[f7])).
% 2.98/0.98  
% 2.98/0.98  fof(f26,plain,(
% 2.98/0.98    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.98/0.98    inference(nnf_transformation,[],[f20])).
% 2.98/0.98  
% 2.98/0.98  fof(f27,plain,(
% 2.98/0.98    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.98/0.98    inference(rectify,[],[f26])).
% 2.98/0.98  
% 2.98/0.98  fof(f30,plain,(
% 2.98/0.98    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)))),
% 2.98/0.98    introduced(choice_axiom,[])).
% 2.98/0.98  
% 2.98/0.98  fof(f29,plain,(
% 2.98/0.98    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(X3,sK1(X0,X1,X2)),X0)))) )),
% 2.98/0.98    introduced(choice_axiom,[])).
% 2.98/0.98  
% 2.98/0.98  fof(f28,plain,(
% 2.98/0.98    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.98/0.98    introduced(choice_axiom,[])).
% 2.98/0.98  
% 2.98/0.98  fof(f31,plain,(
% 2.98/0.98    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.98/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30,f29,f28])).
% 2.98/0.98  
% 2.98/0.98  fof(f55,plain,(
% 2.98/0.98    ( ! [X6,X2,X0,X1] : (r2_hidden(sK2(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 2.98/0.98    inference(cnf_transformation,[],[f31])).
% 2.98/0.98  
% 2.98/0.98  fof(f76,plain,(
% 2.98/0.98    ( ! [X6,X0,X1] : (r2_hidden(sK2(X0,X1,X6),X1) | ~r2_hidden(X6,k10_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.98/0.98    inference(equality_resolution,[],[f55])).
% 2.98/0.98  
% 2.98/0.98  fof(f54,plain,(
% 2.98/0.98    ( ! [X6,X2,X0,X1] : (r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 2.98/0.98    inference(cnf_transformation,[],[f31])).
% 2.98/0.98  
% 2.98/0.98  fof(f77,plain,(
% 2.98/0.98    ( ! [X6,X0,X1] : (r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) | ~r2_hidden(X6,k10_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.98/0.98    inference(equality_resolution,[],[f54])).
% 2.98/0.98  
% 2.98/0.98  fof(f11,conjecture,(
% 2.98/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 2.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f12,negated_conjecture,(
% 2.98/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 2.98/0.98    inference(negated_conjecture,[],[f11])).
% 2.98/0.98  
% 2.98/0.98  fof(f23,plain,(
% 2.98/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.98/0.98    inference(ennf_transformation,[],[f12])).
% 2.98/0.98  
% 2.98/0.98  fof(f36,plain,(
% 2.98/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.98/0.98    inference(nnf_transformation,[],[f23])).
% 2.98/0.98  
% 2.98/0.98  fof(f37,plain,(
% 2.98/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.98/0.98    inference(flattening,[],[f36])).
% 2.98/0.98  
% 2.98/0.98  fof(f38,plain,(
% 2.98/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.98/0.98    inference(rectify,[],[f37])).
% 2.98/0.98  
% 2.98/0.98  fof(f44,plain,(
% 2.98/0.98    ( ! [X4,X2,X3,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK9,X1) & r2_hidden(k4_tarski(X4,sK9),X3) & m1_subset_1(sK9,X2))) )),
% 2.98/0.98    introduced(choice_axiom,[])).
% 2.98/0.98  
% 2.98/0.98  fof(f43,plain,(
% 2.98/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) => ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(sK8,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(sK8,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(sK8,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(sK8,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(sK8,X0))) )),
% 2.98/0.98    introduced(choice_axiom,[])).
% 2.98/0.98  
% 2.98/0.98  fof(f42,plain,(
% 2.98/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),sK7) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,sK7,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),sK7) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,sK7,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))) )),
% 2.98/0.98    introduced(choice_axiom,[])).
% 2.98/0.98  
% 2.98/0.98  fof(f41,plain,(
% 2.98/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,sK6)) | ~r2_hidden(X4,k8_relset_1(X0,sK6,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,sK6)) | r2_hidden(X4,k8_relset_1(X0,sK6,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,sK6)))) & ~v1_xboole_0(sK6))) )),
% 2.98/0.98    introduced(choice_axiom,[])).
% 2.98/0.98  
% 2.98/0.98  fof(f40,plain,(
% 2.98/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,sK5) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,sK5))) & (? [X6] : (r2_hidden(X6,sK5) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,sK5))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK5))) )),
% 2.98/0.98    introduced(choice_axiom,[])).
% 2.98/0.98  
% 2.98/0.98  fof(f39,plain,(
% 2.98/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(sK4,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(sK4,X2,X3,X1))) & m1_subset_1(X4,sK4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,X2)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK4))),
% 2.98/0.98    introduced(choice_axiom,[])).
% 2.98/0.98  
% 2.98/0.98  fof(f45,plain,(
% 2.98/0.98    (((((! [X5] : (~r2_hidden(X5,sK5) | ~r2_hidden(k4_tarski(sK8,X5),sK7) | ~m1_subset_1(X5,sK6)) | ~r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5))) & ((r2_hidden(sK9,sK5) & r2_hidden(k4_tarski(sK8,sK9),sK7) & m1_subset_1(sK9,sK6)) | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5))) & m1_subset_1(sK8,sK4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))) & ~v1_xboole_0(sK6)) & ~v1_xboole_0(sK5)) & ~v1_xboole_0(sK4)),
% 2.98/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f38,f44,f43,f42,f41,f40,f39])).
% 2.98/0.98  
% 2.98/0.98  fof(f69,plain,(
% 2.98/0.98    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))),
% 2.98/0.98    inference(cnf_transformation,[],[f45])).
% 2.98/0.98  
% 2.98/0.98  fof(f4,axiom,(
% 2.98/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f16,plain,(
% 2.98/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.98/0.98    inference(ennf_transformation,[],[f4])).
% 2.98/0.98  
% 2.98/0.98  fof(f17,plain,(
% 2.98/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.98/0.98    inference(flattening,[],[f16])).
% 2.98/0.98  
% 2.98/0.98  fof(f51,plain,(
% 2.98/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.98/0.98    inference(cnf_transformation,[],[f17])).
% 2.98/0.98  
% 2.98/0.98  fof(f3,axiom,(
% 2.98/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f14,plain,(
% 2.98/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.98/0.98    inference(ennf_transformation,[],[f3])).
% 2.98/0.98  
% 2.98/0.98  fof(f15,plain,(
% 2.98/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.98/0.98    inference(flattening,[],[f14])).
% 2.98/0.98  
% 2.98/0.98  fof(f50,plain,(
% 2.98/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.98/0.98    inference(cnf_transformation,[],[f15])).
% 2.98/0.98  
% 2.98/0.98  fof(f5,axiom,(
% 2.98/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f18,plain,(
% 2.98/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.98/0.98    inference(ennf_transformation,[],[f5])).
% 2.98/0.98  
% 2.98/0.98  fof(f52,plain,(
% 2.98/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.98/0.98    inference(cnf_transformation,[],[f18])).
% 2.98/0.98  
% 2.98/0.98  fof(f1,axiom,(
% 2.98/0.98    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f24,plain,(
% 2.98/0.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.98/0.98    inference(nnf_transformation,[],[f1])).
% 2.98/0.98  
% 2.98/0.98  fof(f25,plain,(
% 2.98/0.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.98/0.98    inference(flattening,[],[f24])).
% 2.98/0.98  
% 2.98/0.98  fof(f47,plain,(
% 2.98/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.98/0.98    inference(cnf_transformation,[],[f25])).
% 2.98/0.98  
% 2.98/0.98  fof(f6,axiom,(
% 2.98/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f19,plain,(
% 2.98/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.98/0.98    inference(ennf_transformation,[],[f6])).
% 2.98/0.98  
% 2.98/0.98  fof(f53,plain,(
% 2.98/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.98/0.98    inference(cnf_transformation,[],[f19])).
% 2.98/0.98  
% 2.98/0.98  fof(f8,axiom,(
% 2.98/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f60,plain,(
% 2.98/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.98/0.98    inference(cnf_transformation,[],[f8])).
% 2.98/0.98  
% 2.98/0.98  fof(f2,axiom,(
% 2.98/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f13,plain,(
% 2.98/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.98/0.98    inference(ennf_transformation,[],[f2])).
% 2.98/0.98  
% 2.98/0.98  fof(f49,plain,(
% 2.98/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.98/0.98    inference(cnf_transformation,[],[f13])).
% 2.98/0.98  
% 2.98/0.98  fof(f71,plain,(
% 2.98/0.98    m1_subset_1(sK9,sK6) | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5))),
% 2.98/0.98    inference(cnf_transformation,[],[f45])).
% 2.98/0.98  
% 2.98/0.98  fof(f74,plain,(
% 2.98/0.98    ( ! [X5] : (~r2_hidden(X5,sK5) | ~r2_hidden(k4_tarski(sK8,X5),sK7) | ~m1_subset_1(X5,sK6) | ~r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5))) )),
% 2.98/0.98    inference(cnf_transformation,[],[f45])).
% 2.98/0.98  
% 2.98/0.98  fof(f10,axiom,(
% 2.98/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.98  
% 2.98/0.98  fof(f22,plain,(
% 2.98/0.98    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.98/0.98    inference(ennf_transformation,[],[f10])).
% 2.98/0.98  
% 2.98/0.98  fof(f65,plain,(
% 2.98/0.98    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.98/0.98    inference(cnf_transformation,[],[f22])).
% 2.98/0.98  
% 2.98/0.98  fof(f72,plain,(
% 2.98/0.98    r2_hidden(k4_tarski(sK8,sK9),sK7) | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5))),
% 2.98/0.98    inference(cnf_transformation,[],[f45])).
% 2.98/0.98  
% 2.98/0.98  fof(f73,plain,(
% 2.98/0.98    r2_hidden(sK9,sK5) | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5))),
% 2.98/0.98    inference(cnf_transformation,[],[f45])).
% 2.98/0.98  
% 2.98/0.98  fof(f56,plain,(
% 2.98/0.98    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 2.98/0.98    inference(cnf_transformation,[],[f31])).
% 2.98/0.98  
% 2.98/0.98  fof(f75,plain,(
% 2.98/0.98    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k10_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~v1_relat_1(X0)) )),
% 2.98/0.98    inference(equality_resolution,[],[f56])).
% 2.98/0.98  
% 2.98/0.98  cnf(c_12,plain,
% 2.98/0.98      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 2.98/0.98      | r2_hidden(sK2(X1,X2,X0),X2)
% 2.98/0.98      | ~ v1_relat_1(X1) ),
% 2.98/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1111,plain,
% 2.98/0.98      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 2.98/0.98      | r2_hidden(sK2(X1,X2,X0),X2) = iProver_top
% 2.98/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_13,plain,
% 2.98/0.98      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 2.98/0.98      | r2_hidden(k4_tarski(X0,sK2(X1,X2,X0)),X1)
% 2.98/0.98      | ~ v1_relat_1(X1) ),
% 2.98/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1110,plain,
% 2.98/0.98      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 2.98/0.98      | r2_hidden(k4_tarski(X0,sK2(X1,X2,X0)),X1) = iProver_top
% 2.98/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_25,negated_conjecture,
% 2.98/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
% 2.98/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1099,plain,
% 2.98/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_5,plain,
% 2.98/0.98      ( m1_subset_1(X0,X1)
% 2.98/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.98/0.98      | ~ r2_hidden(X0,X2) ),
% 2.98/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1118,plain,
% 2.98/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 2.98/0.98      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.98/0.98      | r2_hidden(X0,X2) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2440,plain,
% 2.98/0.98      ( m1_subset_1(X0,k2_zfmisc_1(sK4,sK6)) = iProver_top
% 2.98/0.98      | r2_hidden(X0,sK7) != iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_1099,c_1118]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4,plain,
% 2.98/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.98/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1119,plain,
% 2.98/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 2.98/0.98      | r2_hidden(X0,X1) = iProver_top
% 2.98/0.98      | v1_xboole_0(X1) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2655,plain,
% 2.98/0.98      ( r2_hidden(X0,k2_zfmisc_1(sK4,sK6)) = iProver_top
% 2.98/0.98      | r2_hidden(X0,sK7) != iProver_top
% 2.98/0.98      | v1_xboole_0(k2_zfmisc_1(sK4,sK6)) = iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_2440,c_1119]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_6,plain,
% 2.98/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.98/0.98      | ~ r2_hidden(X2,X0)
% 2.98/0.98      | ~ v1_xboole_0(X1) ),
% 2.98/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1117,plain,
% 2.98/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.98/0.98      | r2_hidden(X2,X0) != iProver_top
% 2.98/0.98      | v1_xboole_0(X1) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2432,plain,
% 2.98/0.98      ( r2_hidden(X0,sK7) != iProver_top
% 2.98/0.98      | v1_xboole_0(k2_zfmisc_1(sK4,sK6)) != iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_1099,c_1117]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4128,plain,
% 2.98/0.98      ( r2_hidden(X0,sK7) != iProver_top
% 2.98/0.98      | r2_hidden(X0,k2_zfmisc_1(sK4,sK6)) = iProver_top ),
% 2.98/0.98      inference(global_propositional_subsumption,
% 2.98/0.98                [status(thm)],
% 2.98/0.98                [c_2655,c_2432]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4129,plain,
% 2.98/0.98      ( r2_hidden(X0,k2_zfmisc_1(sK4,sK6)) = iProver_top
% 2.98/0.98      | r2_hidden(X0,sK7) != iProver_top ),
% 2.98/0.98      inference(renaming,[status(thm)],[c_4128]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1,plain,
% 2.98/0.98      ( r2_hidden(X0,X1)
% 2.98/0.98      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 2.98/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1122,plain,
% 2.98/0.98      ( r2_hidden(X0,X1) = iProver_top
% 2.98/0.98      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4137,plain,
% 2.98/0.98      ( r2_hidden(X0,sK6) = iProver_top
% 2.98/0.98      | r2_hidden(k4_tarski(X1,X0),sK7) != iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_4129,c_1122]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4477,plain,
% 2.98/0.98      ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 2.98/0.98      | r2_hidden(sK2(sK7,X1,X0),sK6) = iProver_top
% 2.98/0.98      | v1_relat_1(sK7) != iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_1110,c_4137]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_7,plain,
% 2.98/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.98/0.98      | ~ v1_relat_1(X1)
% 2.98/0.98      | v1_relat_1(X0) ),
% 2.98/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1116,plain,
% 2.98/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.98/0.98      | v1_relat_1(X1) != iProver_top
% 2.98/0.98      | v1_relat_1(X0) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2158,plain,
% 2.98/0.98      ( v1_relat_1(k2_zfmisc_1(sK4,sK6)) != iProver_top
% 2.98/0.98      | v1_relat_1(sK7) = iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_1099,c_1116]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_14,plain,
% 2.98/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.98/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1109,plain,
% 2.98/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2253,plain,
% 2.98/0.98      ( v1_relat_1(sK7) = iProver_top ),
% 2.98/0.98      inference(forward_subsumption_resolution,
% 2.98/0.98                [status(thm)],
% 2.98/0.98                [c_2158,c_1109]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_5324,plain,
% 2.98/0.98      ( r2_hidden(sK2(sK7,X1,X0),sK6) = iProver_top
% 2.98/0.98      | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top ),
% 2.98/0.98      inference(global_propositional_subsumption,
% 2.98/0.98                [status(thm)],
% 2.98/0.98                [c_4477,c_2253]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_5325,plain,
% 2.98/0.98      ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 2.98/0.98      | r2_hidden(sK2(sK7,X1,X0),sK6) = iProver_top ),
% 2.98/0.98      inference(renaming,[status(thm)],[c_5324]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3,plain,
% 2.98/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.98/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1120,plain,
% 2.98/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 2.98/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_5332,plain,
% 2.98/0.98      ( m1_subset_1(sK2(sK7,X0,X1),sK6) = iProver_top
% 2.98/0.98      | r2_hidden(X1,k10_relat_1(sK7,X0)) != iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_5325,c_1120]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_23,negated_conjecture,
% 2.98/0.98      ( m1_subset_1(sK9,sK6)
% 2.98/0.98      | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
% 2.98/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1101,plain,
% 2.98/0.98      ( m1_subset_1(sK9,sK6) = iProver_top
% 2.98/0.98      | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_20,negated_conjecture,
% 2.98/0.98      ( ~ m1_subset_1(X0,sK6)
% 2.98/0.98      | ~ r2_hidden(X0,sK5)
% 2.98/0.98      | ~ r2_hidden(k4_tarski(sK8,X0),sK7)
% 2.98/0.98      | ~ r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
% 2.98/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1104,plain,
% 2.98/0.98      ( m1_subset_1(X0,sK6) != iProver_top
% 2.98/0.98      | r2_hidden(X0,sK5) != iProver_top
% 2.98/0.98      | r2_hidden(k4_tarski(sK8,X0),sK7) != iProver_top
% 2.98/0.98      | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1446,plain,
% 2.98/0.98      ( m1_subset_1(X0,sK6) != iProver_top
% 2.98/0.98      | m1_subset_1(sK9,sK6) = iProver_top
% 2.98/0.98      | r2_hidden(X0,sK5) != iProver_top
% 2.98/0.98      | r2_hidden(k4_tarski(sK8,X0),sK7) != iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_1101,c_1104]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3289,plain,
% 2.98/0.98      ( m1_subset_1(sK2(sK7,X0,sK8),sK6) != iProver_top
% 2.98/0.98      | m1_subset_1(sK9,sK6) = iProver_top
% 2.98/0.98      | r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
% 2.98/0.98      | v1_relat_1(sK7) != iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_1110,c_1446]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3479,plain,
% 2.98/0.98      ( r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
% 2.98/0.98      | r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
% 2.98/0.98      | m1_subset_1(sK9,sK6) = iProver_top
% 2.98/0.98      | m1_subset_1(sK2(sK7,X0,sK8),sK6) != iProver_top ),
% 2.98/0.98      inference(global_propositional_subsumption,
% 2.98/0.98                [status(thm)],
% 2.98/0.98                [c_3289,c_2253]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3480,plain,
% 2.98/0.98      ( m1_subset_1(sK2(sK7,X0,sK8),sK6) != iProver_top
% 2.98/0.98      | m1_subset_1(sK9,sK6) = iProver_top
% 2.98/0.98      | r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top ),
% 2.98/0.98      inference(renaming,[status(thm)],[c_3479]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_5639,plain,
% 2.98/0.98      ( m1_subset_1(sK9,sK6) = iProver_top
% 2.98/0.98      | r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_5332,c_3480]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_19,plain,
% 2.98/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.98      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.98/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1105,plain,
% 2.98/0.98      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.98/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2357,plain,
% 2.98/0.98      ( k8_relset_1(sK4,sK6,sK7,X0) = k10_relat_1(sK7,X0) ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_1099,c_1105]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_22,negated_conjecture,
% 2.98/0.98      ( r2_hidden(k4_tarski(sK8,sK9),sK7)
% 2.98/0.98      | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
% 2.98/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1102,plain,
% 2.98/0.98      ( r2_hidden(k4_tarski(sK8,sK9),sK7) = iProver_top
% 2.98/0.98      | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2581,plain,
% 2.98/0.98      ( r2_hidden(k4_tarski(sK8,sK9),sK7) = iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
% 2.98/0.98      inference(demodulation,[status(thm)],[c_2357,c_1102]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4479,plain,
% 2.98/0.98      ( r2_hidden(sK9,sK6) = iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_2581,c_4137]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_21,negated_conjecture,
% 2.98/0.98      ( r2_hidden(sK9,sK5)
% 2.98/0.98      | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
% 2.98/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1103,plain,
% 2.98/0.98      ( r2_hidden(sK9,sK5) = iProver_top
% 2.98/0.98      | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) = iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2582,plain,
% 2.98/0.98      ( r2_hidden(sK9,sK5) = iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
% 2.98/0.98      inference(demodulation,[status(thm)],[c_2357,c_1103]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_11,plain,
% 2.98/0.98      ( ~ r2_hidden(X0,X1)
% 2.98/0.98      | r2_hidden(X2,k10_relat_1(X3,X1))
% 2.98/0.98      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 2.98/0.98      | ~ v1_relat_1(X3) ),
% 2.98/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_1112,plain,
% 2.98/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.98/0.98      | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
% 2.98/0.98      | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
% 2.98/0.98      | v1_relat_1(X3) != iProver_top ),
% 2.98/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3731,plain,
% 2.98/0.98      ( r2_hidden(sK9,X0) != iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,X0)) = iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top
% 2.98/0.98      | v1_relat_1(sK7) != iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_2581,c_1112]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4180,plain,
% 2.98/0.98      ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,X0)) = iProver_top
% 2.98/0.98      | r2_hidden(sK9,X0) != iProver_top ),
% 2.98/0.98      inference(global_propositional_subsumption,
% 2.98/0.98                [status(thm)],
% 2.98/0.98                [c_3731,c_2253]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4181,plain,
% 2.98/0.98      ( r2_hidden(sK9,X0) != iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,X0)) = iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
% 2.98/0.98      inference(renaming,[status(thm)],[c_4180]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4191,plain,
% 2.98/0.98      ( r2_hidden(sK9,sK5) != iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top
% 2.98/0.98      | iProver_top != iProver_top ),
% 2.98/0.98      inference(equality_factoring,[status(thm)],[c_4181]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4193,plain,
% 2.98/0.98      ( r2_hidden(sK9,sK5) != iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
% 2.98/0.98      inference(equality_resolution_simp,[status(thm)],[c_4191]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4509,plain,
% 2.98/0.98      ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
% 2.98/0.98      inference(global_propositional_subsumption,
% 2.98/0.98                [status(thm)],
% 2.98/0.98                [c_4479,c_2582,c_4193]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_2584,plain,
% 2.98/0.98      ( m1_subset_1(X0,sK6) != iProver_top
% 2.98/0.98      | r2_hidden(X0,sK5) != iProver_top
% 2.98/0.98      | r2_hidden(k4_tarski(sK8,X0),sK7) != iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top ),
% 2.98/0.98      inference(demodulation,[status(thm)],[c_2357,c_1104]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_3286,plain,
% 2.98/0.98      ( m1_subset_1(sK2(sK7,X0,sK8),sK6) != iProver_top
% 2.98/0.98      | r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top
% 2.98/0.98      | v1_relat_1(sK7) != iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_1110,c_2584]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4039,plain,
% 2.98/0.98      ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
% 2.98/0.98      | r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
% 2.98/0.98      | m1_subset_1(sK2(sK7,X0,sK8),sK6) != iProver_top ),
% 2.98/0.98      inference(global_propositional_subsumption,
% 2.98/0.98                [status(thm)],
% 2.98/0.98                [c_3286,c_2253]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_4040,plain,
% 2.98/0.98      ( m1_subset_1(sK2(sK7,X0,sK8),sK6) != iProver_top
% 2.98/0.98      | r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top ),
% 2.98/0.98      inference(renaming,[status(thm)],[c_4039]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_5637,plain,
% 2.98/0.98      ( r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_5332,c_4040]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_6020,plain,
% 2.98/0.98      ( r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
% 2.98/0.98      | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top ),
% 2.98/0.98      inference(global_propositional_subsumption,
% 2.98/0.98                [status(thm)],
% 2.98/0.98                [c_5639,c_2582,c_4193,c_5637]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(c_6028,plain,
% 2.98/0.98      ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top
% 2.98/0.98      | v1_relat_1(sK7) != iProver_top ),
% 2.98/0.98      inference(superposition,[status(thm)],[c_1111,c_6020]) ).
% 2.98/0.98  
% 2.98/0.98  cnf(contradiction,plain,
% 2.98/0.98      ( $false ),
% 2.98/0.98      inference(minisat,[status(thm)],[c_6028,c_4509,c_2253]) ).
% 2.98/0.98  
% 2.98/0.98  
% 2.98/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.98/0.98  
% 2.98/0.98  ------                               Statistics
% 2.98/0.98  
% 2.98/0.98  ------ General
% 2.98/0.98  
% 2.98/0.98  abstr_ref_over_cycles:                  0
% 2.98/0.98  abstr_ref_under_cycles:                 0
% 2.98/0.98  gc_basic_clause_elim:                   0
% 2.98/0.98  forced_gc_time:                         0
% 2.98/0.98  parsing_time:                           0.009
% 2.98/0.98  unif_index_cands_time:                  0.
% 2.98/0.98  unif_index_add_time:                    0.
% 2.98/0.98  orderings_time:                         0.
% 2.98/0.98  out_proof_time:                         0.009
% 2.98/0.98  total_time:                             0.207
% 2.98/0.98  num_of_symbols:                         51
% 2.98/0.98  num_of_terms:                           7008
% 2.98/0.98  
% 2.98/0.98  ------ Preprocessing
% 2.98/0.98  
% 2.98/0.98  num_of_splits:                          0
% 2.98/0.98  num_of_split_atoms:                     0
% 2.98/0.98  num_of_reused_defs:                     0
% 2.98/0.98  num_eq_ax_congr_red:                    45
% 2.98/0.98  num_of_sem_filtered_clauses:            1
% 2.98/0.98  num_of_subtypes:                        0
% 2.98/0.98  monotx_restored_types:                  0
% 2.98/0.98  sat_num_of_epr_types:                   0
% 2.98/0.98  sat_num_of_non_cyclic_types:            0
% 2.98/0.98  sat_guarded_non_collapsed_types:        0
% 2.98/0.98  num_pure_diseq_elim:                    0
% 2.98/0.98  simp_replaced_by:                       0
% 2.98/0.98  res_preprocessed:                       133
% 2.98/0.98  prep_upred:                             0
% 2.98/0.98  prep_unflattend:                        6
% 2.98/0.98  smt_new_axioms:                         0
% 2.98/0.98  pred_elim_cands:                        4
% 2.98/0.98  pred_elim:                              0
% 2.98/0.98  pred_elim_cl:                           0
% 2.98/0.98  pred_elim_cycles:                       2
% 2.98/0.98  merged_defs:                            0
% 2.98/0.98  merged_defs_ncl:                        0
% 2.98/0.98  bin_hyper_res:                          0
% 2.98/0.98  prep_cycles:                            4
% 2.98/0.98  pred_elim_time:                         0.003
% 2.98/0.98  splitting_time:                         0.
% 2.98/0.98  sem_filter_time:                        0.
% 2.98/0.98  monotx_time:                            0.001
% 2.98/0.98  subtype_inf_time:                       0.
% 2.98/0.98  
% 2.98/0.98  ------ Problem properties
% 2.98/0.98  
% 2.98/0.98  clauses:                                28
% 2.98/0.98  conjectures:                            9
% 2.98/0.98  epr:                                    6
% 2.98/0.98  horn:                                   22
% 2.98/0.98  ground:                                 8
% 2.98/0.98  unary:                                  6
% 2.98/0.98  binary:                                 7
% 2.98/0.98  lits:                                   71
% 2.98/0.98  lits_eq:                                4
% 2.98/0.98  fd_pure:                                0
% 2.98/0.98  fd_pseudo:                              0
% 2.98/0.98  fd_cond:                                0
% 2.98/0.98  fd_pseudo_cond:                         3
% 2.98/0.98  ac_symbols:                             0
% 2.98/0.98  
% 2.98/0.98  ------ Propositional Solver
% 2.98/0.98  
% 2.98/0.98  prop_solver_calls:                      26
% 2.98/0.98  prop_fast_solver_calls:                 1004
% 2.98/0.98  smt_solver_calls:                       0
% 2.98/0.98  smt_fast_solver_calls:                  0
% 2.98/0.98  prop_num_of_clauses:                    2484
% 2.98/0.98  prop_preprocess_simplified:             5980
% 2.98/0.98  prop_fo_subsumed:                       23
% 2.98/0.98  prop_solver_time:                       0.
% 2.98/0.98  smt_solver_time:                        0.
% 2.98/0.98  smt_fast_solver_time:                   0.
% 2.98/0.98  prop_fast_solver_time:                  0.
% 2.98/0.98  prop_unsat_core_time:                   0.
% 2.98/0.98  
% 2.98/0.98  ------ QBF
% 2.98/0.98  
% 2.98/0.98  qbf_q_res:                              0
% 2.98/0.98  qbf_num_tautologies:                    0
% 2.98/0.98  qbf_prep_cycles:                        0
% 2.98/0.98  
% 2.98/0.98  ------ BMC1
% 2.98/0.98  
% 2.98/0.98  bmc1_current_bound:                     -1
% 2.98/0.98  bmc1_last_solved_bound:                 -1
% 2.98/0.98  bmc1_unsat_core_size:                   -1
% 2.98/0.98  bmc1_unsat_core_parents_size:           -1
% 2.98/0.98  bmc1_merge_next_fun:                    0
% 2.98/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.98/0.98  
% 2.98/0.98  ------ Instantiation
% 2.98/0.98  
% 2.98/0.98  inst_num_of_clauses:                    658
% 2.98/0.98  inst_num_in_passive:                    37
% 2.98/0.98  inst_num_in_active:                     309
% 2.98/0.98  inst_num_in_unprocessed:                312
% 2.98/0.98  inst_num_of_loops:                      380
% 2.98/0.98  inst_num_of_learning_restarts:          0
% 2.98/0.98  inst_num_moves_active_passive:          68
% 2.98/0.98  inst_lit_activity:                      0
% 2.98/0.98  inst_lit_activity_moves:                0
% 2.98/0.98  inst_num_tautologies:                   0
% 2.98/0.98  inst_num_prop_implied:                  0
% 2.98/0.98  inst_num_existing_simplified:           0
% 2.98/0.98  inst_num_eq_res_simplified:             0
% 2.98/0.98  inst_num_child_elim:                    0
% 2.98/0.98  inst_num_of_dismatching_blockings:      80
% 2.98/0.98  inst_num_of_non_proper_insts:           376
% 2.98/0.98  inst_num_of_duplicates:                 0
% 2.98/0.98  inst_inst_num_from_inst_to_res:         0
% 2.98/0.98  inst_dismatching_checking_time:         0.
% 2.98/0.98  
% 2.98/0.98  ------ Resolution
% 2.98/0.98  
% 2.98/0.98  res_num_of_clauses:                     0
% 2.98/0.98  res_num_in_passive:                     0
% 2.98/0.98  res_num_in_active:                      0
% 2.98/0.98  res_num_of_loops:                       137
% 2.98/0.98  res_forward_subset_subsumed:            17
% 2.98/0.98  res_backward_subset_subsumed:           0
% 2.98/0.98  res_forward_subsumed:                   0
% 2.98/0.98  res_backward_subsumed:                  0
% 2.98/0.98  res_forward_subsumption_resolution:     0
% 2.98/0.98  res_backward_subsumption_resolution:    0
% 2.98/0.98  res_clause_to_clause_subsumption:       247
% 2.98/0.98  res_orphan_elimination:                 0
% 2.98/0.98  res_tautology_del:                      25
% 2.98/0.98  res_num_eq_res_simplified:              0
% 2.98/0.98  res_num_sel_changes:                    0
% 2.98/0.98  res_moves_from_active_to_pass:          0
% 2.98/0.98  
% 2.98/0.98  ------ Superposition
% 2.98/0.98  
% 2.98/0.98  sup_time_total:                         0.
% 2.98/0.98  sup_time_generating:                    0.
% 2.98/0.98  sup_time_sim_full:                      0.
% 2.98/0.98  sup_time_sim_immed:                     0.
% 2.98/0.98  
% 2.98/0.98  sup_num_of_clauses:                     127
% 2.98/0.98  sup_num_in_active:                      67
% 2.98/0.98  sup_num_in_passive:                     60
% 2.98/0.98  sup_num_of_loops:                       75
% 2.98/0.98  sup_fw_superposition:                   51
% 2.98/0.98  sup_bw_superposition:                   88
% 2.98/0.98  sup_immediate_simplified:               22
% 2.98/0.98  sup_given_eliminated:                   0
% 2.98/0.98  comparisons_done:                       0
% 2.98/0.98  comparisons_avoided:                    0
% 2.98/0.98  
% 2.98/0.98  ------ Simplifications
% 2.98/0.98  
% 2.98/0.98  
% 2.98/0.98  sim_fw_subset_subsumed:                 21
% 2.98/0.98  sim_bw_subset_subsumed:                 4
% 2.98/0.98  sim_fw_subsumed:                        1
% 2.98/0.98  sim_bw_subsumed:                        0
% 2.98/0.98  sim_fw_subsumption_res:                 1
% 2.98/0.98  sim_bw_subsumption_res:                 0
% 2.98/0.98  sim_tautology_del:                      6
% 2.98/0.98  sim_eq_tautology_del:                   0
% 2.98/0.98  sim_eq_res_simp:                        1
% 2.98/0.98  sim_fw_demodulated:                     0
% 2.98/0.98  sim_bw_demodulated:                     7
% 2.98/0.98  sim_light_normalised:                   0
% 2.98/0.98  sim_joinable_taut:                      0
% 2.98/0.98  sim_joinable_simp:                      0
% 2.98/0.98  sim_ac_normalised:                      0
% 2.98/0.98  sim_smt_subsumption:                    0
% 2.98/0.98  
%------------------------------------------------------------------------------

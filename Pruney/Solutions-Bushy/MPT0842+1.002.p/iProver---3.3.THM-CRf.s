%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0842+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:14 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 579 expanded)
%              Number of clauses        :   60 ( 140 expanded)
%              Number of leaves         :   18 ( 202 expanded)
%              Depth                    :   20
%              Number of atoms          :  526 (5436 expanded)
%              Number of equality atoms :  120 ( 275 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK1(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25,f24,f23])).

fof(f40,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f37,plain,(
    ! [X4,X2,X3,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X4,X6),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK8,X1)
        & r2_hidden(k4_tarski(X4,sK8),X3)
        & m1_subset_1(sK8,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
              | ~ r2_hidden(k4_tarski(sK7,X5),X3)
              | ~ m1_subset_1(X5,X2) )
          | ~ r2_hidden(sK7,k8_relset_1(X0,X2,X3,X1)) )
        & ( ? [X6] :
              ( r2_hidden(X6,X1)
              & r2_hidden(k4_tarski(sK7,X6),X3)
              & m1_subset_1(X6,X2) )
          | r2_hidden(sK7,k8_relset_1(X0,X2,X3,X1)) )
        & m1_subset_1(sK7,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
                  | ~ r2_hidden(k4_tarski(X4,X5),sK6)
                  | ~ m1_subset_1(X5,X2) )
              | ~ r2_hidden(X4,k8_relset_1(X0,X2,sK6,X1)) )
            & ( ? [X6] :
                  ( r2_hidden(X6,X1)
                  & r2_hidden(k4_tarski(X4,X6),sK6)
                  & m1_subset_1(X6,X2) )
              | r2_hidden(X4,k8_relset_1(X0,X2,sK6,X1)) )
            & m1_subset_1(X4,X0) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
                      | ~ m1_subset_1(X5,sK5) )
                  | ~ r2_hidden(X4,k8_relset_1(X0,sK5,X3,X1)) )
                & ( ? [X6] :
                      ( r2_hidden(X6,X1)
                      & r2_hidden(k4_tarski(X4,X6),X3)
                      & m1_subset_1(X6,sK5) )
                  | r2_hidden(X4,k8_relset_1(X0,sK5,X3,X1)) )
                & m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,sK5))) )
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
                          ( ~ r2_hidden(X5,sK4)
                          | ~ r2_hidden(k4_tarski(X4,X5),X3)
                          | ~ m1_subset_1(X5,X2) )
                      | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,sK4)) )
                    & ( ? [X6] :
                          ( r2_hidden(X6,sK4)
                          & r2_hidden(k4_tarski(X4,X6),X3)
                          & m1_subset_1(X6,X2) )
                      | r2_hidden(X4,k8_relset_1(X0,X2,X3,sK4)) )
                    & m1_subset_1(X4,X0) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
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
                        | ~ r2_hidden(X4,k8_relset_1(sK3,X2,X3,X1)) )
                      & ( ? [X6] :
                            ( r2_hidden(X6,X1)
                            & r2_hidden(k4_tarski(X4,X6),X3)
                            & m1_subset_1(X6,X2) )
                        | r2_hidden(X4,k8_relset_1(sK3,X2,X3,X1)) )
                      & m1_subset_1(X4,sK3) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X2))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ! [X5] :
          ( ~ r2_hidden(X5,sK4)
          | ~ r2_hidden(k4_tarski(sK7,X5),sK6)
          | ~ m1_subset_1(X5,sK5) )
      | ~ r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) )
    & ( ( r2_hidden(sK8,sK4)
        & r2_hidden(k4_tarski(sK7,sK8),sK6)
        & m1_subset_1(sK8,sK5) )
      | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) )
    & m1_subset_1(sK7,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    & ~ v1_xboole_0(sK5)
    & ~ v1_xboole_0(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f31,f37,f36,f35,f34,f33,f32])).

fof(f57,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f61,plain,
    ( r2_hidden(sK8,sK4)
    | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK4)
      | ~ r2_hidden(k4_tarski(sK7,X5),sK6)
      | ~ m1_subset_1(X5,sK5)
      | ~ r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),sK6)
    | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) ),
    inference(cnf_transformation,[],[f38])).

fof(f42,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK2(X1,X2,X0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_877,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(X1,X2,X0)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_863,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_870,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1857,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | m1_subset_1(X0,k2_zfmisc_1(sK3,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_863,c_870])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_871,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2042,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK3,sK5)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK3,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1857,c_871])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_869,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1784,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK3,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_863,c_869])).

cnf(c_3322,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,k2_zfmisc_1(sK3,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2042,c_1784])).

cnf(c_3323,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK3,sK5)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_3322])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_874,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3332,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3323,c_874])).

cnf(c_3585,plain,
    ( r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_3332])).

cnf(c_27,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1055,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1056,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1055])).

cnf(c_4021,plain,
    ( r2_hidden(sK2(sK6,X1,X0),sK5) = iProver_top
    | r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3585,c_27,c_1056])).

cnf(c_4022,plain,
    ( r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_4021])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_872,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4029,plain,
    ( r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top
    | m1_subset_1(sK2(sK6,X1,X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4022,c_872])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_878,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK2(X1,X2,X0),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK8,sK4)
    | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_867,plain,
    ( r2_hidden(sK8,sK4) = iProver_top
    | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(k4_tarski(sK7,X0),sK6)
    | ~ r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4))
    | ~ m1_subset_1(X0,sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_868,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top
    | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) != iProver_top
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1211,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top
    | r2_hidden(sK8,sK4) = iProver_top
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_867,c_868])).

cnf(c_2350,plain,
    ( r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
    | r2_hidden(sK8,sK4) = iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top
    | m1_subset_1(sK2(sK6,X0,sK7),sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_1211])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_876,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1778,plain,
    ( k8_relset_1(sK3,sK5,sK6,X0) = k10_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_863,c_876])).

cnf(c_1953,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,sK4)) != iProver_top
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1778,c_868])).

cnf(c_2348,plain,
    ( r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,sK4)) != iProver_top
    | m1_subset_1(sK2(sK6,X0,sK7),sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_1953])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(k4_tarski(sK7,sK8),sK6)
    | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_866,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),sK6) = iProver_top
    | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1336,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top
    | r2_hidden(k4_tarski(sK7,sK8),sK6) = iProver_top
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_866,c_868])).

cnf(c_2349,plain,
    ( r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
    | r2_hidden(k4_tarski(sK7,sK8),sK6) = iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top
    | m1_subset_1(sK2(sK6,X0,sK7),sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_1336])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1137,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK6,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1413,plain,
    ( r2_hidden(X0,k10_relat_1(sK6,sK4))
    | ~ r2_hidden(k4_tarski(X0,sK8),sK6)
    | ~ r2_hidden(sK8,sK4)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1137])).

cnf(c_2670,plain,
    ( ~ r2_hidden(k4_tarski(sK7,sK8),sK6)
    | ~ r2_hidden(sK8,sK4)
    | r2_hidden(sK7,k10_relat_1(sK6,sK4))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1413])).

cnf(c_2671,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),sK6) != iProver_top
    | r2_hidden(sK8,sK4) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2670])).

cnf(c_2910,plain,
    ( m1_subset_1(sK2(sK6,X0,sK7),sK5) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top
    | r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2350,c_27,c_1056,c_2348,c_2349,c_2671])).

cnf(c_2911,plain,
    ( r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top
    | m1_subset_1(sK2(sK6,X0,sK7),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_2910])).

cnf(c_2919,plain,
    ( r2_hidden(sK7,k10_relat_1(sK6,sK4)) != iProver_top
    | m1_subset_1(sK2(sK6,sK4,sK7),sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_878,c_2911])).

cnf(c_1950,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),sK6) = iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1778,c_866])).

cnf(c_2191,plain,
    ( r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top
    | m1_subset_1(k4_tarski(sK7,sK8),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1950,c_872])).

cnf(c_1951,plain,
    ( r2_hidden(sK8,sK4) = iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1778,c_867])).

cnf(c_3275,plain,
    ( r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2191,c_27,c_1056,c_1950,c_1951,c_2671])).

cnf(c_3838,plain,
    ( m1_subset_1(sK2(sK6,sK4,sK7),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2919,c_27,c_1056,c_1950,c_1951,c_2671])).

cnf(c_4037,plain,
    ( r2_hidden(sK7,k10_relat_1(sK6,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4029,c_3838])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4037,c_3275])).


%------------------------------------------------------------------------------

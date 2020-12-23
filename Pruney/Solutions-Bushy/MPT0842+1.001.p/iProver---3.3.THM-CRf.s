%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0842+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:14 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 920 expanded)
%              Number of clauses        :   83 ( 226 expanded)
%              Number of leaves         :   20 ( 317 expanded)
%              Depth                    :   22
%              Number of atoms          :  603 (8480 expanded)
%              Number of equality atoms :  172 ( 425 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f3,f28])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f40,plain,(
    ! [X4,X2,X3,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X4,X6),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK9,X1)
        & r2_hidden(k4_tarski(X4,sK9),X3)
        & m1_subset_1(sK9,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f34,f40,f39,f38,f37,f36,f35])).

fof(f62,plain,(
    m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f26,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK1(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25,f24])).

fof(f43,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK7)
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,
    ( r2_hidden(sK9,sK5)
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
    inference(cnf_transformation,[],[f41])).

fof(f45,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f30])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f66,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK5)
      | ~ r2_hidden(k4_tarski(sK8,X5),sK7)
      | ~ m1_subset_1(X5,sK6)
      | ~ r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_7,plain,
    ( m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_900,plain,
    ( m1_subset_1(sK3(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_894,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1995,plain,
    ( r2_hidden(sK3(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_900,c_894])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_887,plain,
    ( m1_subset_1(sK8,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1996,plain,
    ( r2_hidden(sK8,sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_887,c_894])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_25,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_29,plain,
    ( m1_subset_1(sK8,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1106,plain,
    ( r2_hidden(sK8,sK4)
    | ~ m1_subset_1(sK8,sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1107,plain,
    ( r2_hidden(sK8,sK4) = iProver_top
    | m1_subset_1(sK8,sK4) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1106])).

cnf(c_2212,plain,
    ( r2_hidden(sK8,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1996,c_25,c_29,c_1107])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_886,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_893,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1846,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | m1_subset_1(X0,k2_zfmisc_1(sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_886,c_893])).

cnf(c_2136,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK4,sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1846,c_894])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK2(X1,X2,X0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_901,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(X1,X2,X0)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(X2,X1,X3),X3)
    | ~ r2_hidden(k4_tarski(sK0(X2,X1,X3),X0),X2)
    | ~ v1_relat_1(X2)
    | k10_relat_1(X2,X1) = X3 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_906,plain,
    ( k10_relat_1(X0,X1) = X2
    | r2_hidden(X3,X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),X3),X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4198,plain,
    ( k10_relat_1(k2_zfmisc_1(sK4,sK6),X0) = X1
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(sK4,sK6),X0,X1),X1) != iProver_top
    | r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK4,sK6),X0,X1),X2),sK7) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,sK6)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2136,c_906])).

cnf(c_5176,plain,
    ( k10_relat_1(k2_zfmisc_1(sK4,sK6),X0) = X1
    | r2_hidden(sK2(sK7,X2,sK0(k2_zfmisc_1(sK4,sK6),X0,X1)),X0) != iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(sK4,sK6),X0,X1),X1) != iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(sK4,sK6),X0,X1),k10_relat_1(sK7,X2)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,sK6)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK6)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_901,c_4198])).

cnf(c_28,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1095,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1096,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1095])).

cnf(c_7339,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK6)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,sK6)) = iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(sK4,sK6),X0,X1),k10_relat_1(sK7,X2)) != iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(sK4,sK6),X0,X1),X1) != iProver_top
    | r2_hidden(sK2(sK7,X2,sK0(k2_zfmisc_1(sK4,sK6),X0,X1)),X0) != iProver_top
    | k10_relat_1(k2_zfmisc_1(sK4,sK6),X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5176,c_28,c_1096])).

cnf(c_7340,plain,
    ( k10_relat_1(k2_zfmisc_1(sK4,sK6),X0) = X1
    | r2_hidden(sK2(sK7,X2,sK0(k2_zfmisc_1(sK4,sK6),X0,X1)),X0) != iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(sK4,sK6),X0,X1),X1) != iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(sK4,sK6),X0,X1),k10_relat_1(sK7,X2)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,sK6)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7339])).

cnf(c_7352,plain,
    ( k10_relat_1(k2_zfmisc_1(sK4,sK6),k2_zfmisc_1(sK4,sK6)) = X0
    | r2_hidden(sK2(sK7,X1,sK0(k2_zfmisc_1(sK4,sK6),k2_zfmisc_1(sK4,sK6),X0)),sK7) != iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(sK4,sK6),k2_zfmisc_1(sK4,sK6),X0),X0) != iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(sK4,sK6),k2_zfmisc_1(sK4,sK6),X0),k10_relat_1(sK7,X1)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,sK6)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2136,c_7340])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_899,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2020,plain,
    ( k8_relset_1(sK4,sK6,sK7,X0) = k10_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_886,c_899])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(k4_tarski(sK8,sK9),sK7)
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_889,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK7) = iProver_top
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2083,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK7) = iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2020,c_889])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_892,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2591,plain,
    ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2083,c_892])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK9,sK5)
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_890,plain,
    ( r2_hidden(sK9,sK5) = iProver_top
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2084,plain,
    ( r2_hidden(sK9,sK5) = iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2020,c_890])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1185,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK7,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1508,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,sK5))
    | ~ r2_hidden(k4_tarski(X0,sK9),sK7)
    | ~ r2_hidden(sK9,sK5)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1185])).

cnf(c_3228,plain,
    ( ~ r2_hidden(k4_tarski(sK8,sK9),sK7)
    | ~ r2_hidden(sK9,sK5)
    | r2_hidden(sK8,k10_relat_1(sK7,sK5))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1508])).

cnf(c_3229,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK7) != iProver_top
    | r2_hidden(sK9,sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3228])).

cnf(c_3667,plain,
    ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2591,c_28,c_1096,c_2083,c_2084,c_3229])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_897,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4196,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK7) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2136,c_897])).

cnf(c_4769,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK2(sK7,X1,X0),sK6) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,sK6)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_901,c_4196])).

cnf(c_5752,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK4,sK6)) = iProver_top
    | r2_hidden(sK2(sK7,X1,X0),sK6) = iProver_top
    | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4769,c_28,c_1096])).

cnf(c_5753,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK2(sK7,X1,X0),sK6) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5752])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_895,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5761,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | m1_subset_1(sK2(sK7,X1,X0),sK6) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5753,c_895])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_902,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK2(X1,X2,X0),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(k4_tarski(sK8,X0),sK7)
    | ~ r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5))
    | ~ m1_subset_1(X0,sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_891,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(sK8,X0),sK7) != iProver_top
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) != iProver_top
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1259,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(sK8,X0),sK7) != iProver_top
    | r2_hidden(sK9,sK5) = iProver_top
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_890,c_891])).

cnf(c_2973,plain,
    ( r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
    | r2_hidden(sK9,sK5) = iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
    | m1_subset_1(sK2(sK7,X0,sK8),sK6) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_901,c_1259])).

cnf(c_2086,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(sK8,X0),sK7) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2020,c_891])).

cnf(c_2971,plain,
    ( r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top
    | m1_subset_1(sK2(sK7,X0,sK8),sK6) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_901,c_2086])).

cnf(c_3686,plain,
    ( m1_subset_1(sK2(sK7,X0,sK8),sK6) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2973,c_28,c_1096,c_2083,c_2084,c_2971,c_3229])).

cnf(c_3687,plain,
    ( r2_hidden(sK2(sK7,X0,sK8),sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
    | m1_subset_1(sK2(sK7,X0,sK8),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_3686])).

cnf(c_3695,plain,
    ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top
    | m1_subset_1(sK2(sK7,sK5,sK8),sK6) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_902,c_3687])).

cnf(c_4759,plain,
    ( m1_subset_1(sK2(sK7,sK5,sK8),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3695,c_28,c_1096,c_2083,c_2084,c_3229])).

cnf(c_7475,plain,
    ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5761,c_4759])).

cnf(c_7649,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK4,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7352,c_28,c_1096,c_2083,c_2084,c_3229,c_7475])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_898,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2611,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_898,c_892])).

cnf(c_7655,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7649,c_2611])).

cnf(c_7767,plain,
    ( r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2212,c_7655])).

cnf(c_7788,plain,
    ( v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1995,c_7767])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_27,plain,
    ( v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7788,c_27])).


%------------------------------------------------------------------------------

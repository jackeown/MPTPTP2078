%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0840+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:14 EST 2020

% Result     : Theorem 40.04s
% Output     : CNFRefutation 40.04s
% Verified   : 
% Statistics : Number of formulae       :  189 (1431 expanded)
%              Number of clauses        :  120 ( 380 expanded)
%              Number of leaves         :   24 ( 530 expanded)
%              Depth                    :   21
%              Number of atoms          :  782 (12976 expanded)
%              Number of equality atoms :  244 ( 627 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f26])).

fof(f30,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK1(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK0(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f30,f29,f28])).

fof(f49,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                     => ! [X5,X6] :
                          ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
                        <=> ? [X7] :
                              ( r2_hidden(k4_tarski(X7,X6),X4)
                              & r2_hidden(k4_tarski(X5,X7),X3)
                              & m1_subset_1(X7,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                       => ! [X5,X6] :
                            ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
                          <=> ? [X7] :
                                ( r2_hidden(k4_tarski(X7,X6),X4)
                                & r2_hidden(k4_tarski(X5,X7),X3)
                                & m1_subset_1(X7,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5,X6] :
                          ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
                        <~> ? [X7] :
                              ( r2_hidden(k4_tarski(X7,X6),X4)
                              & r2_hidden(k4_tarski(X5,X7),X3)
                              & m1_subset_1(X7,X1) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
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
                      ( ? [X5,X6] :
                          ( ( ! [X7] :
                                ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                                | ~ r2_hidden(k4_tarski(X5,X7),X3)
                                | ~ m1_subset_1(X7,X1) )
                            | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
                          & ( ? [X7] :
                                ( r2_hidden(k4_tarski(X7,X6),X4)
                                & r2_hidden(k4_tarski(X5,X7),X3)
                                & m1_subset_1(X7,X1) )
                            | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5,X6] :
                          ( ( ! [X7] :
                                ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                                | ~ r2_hidden(k4_tarski(X5,X7),X3)
                                | ~ m1_subset_1(X7,X1) )
                            | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
                          & ( ? [X8] :
                                ( r2_hidden(k4_tarski(X8,X6),X4)
                                & r2_hidden(k4_tarski(X5,X8),X3)
                                & m1_subset_1(X8,X1) )
                            | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(rectify,[],[f36])).

fof(f44,plain,(
    ! [X6,X4,X5,X3,X1] :
      ( ? [X8] :
          ( r2_hidden(k4_tarski(X8,X6),X4)
          & r2_hidden(k4_tarski(X5,X8),X3)
          & m1_subset_1(X8,X1) )
     => ( r2_hidden(k4_tarski(sK12,X6),X4)
        & r2_hidden(k4_tarski(X5,sK12),X3)
        & m1_subset_1(sK12,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5,X6] :
          ( ( ! [X7] :
                ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                | ~ r2_hidden(k4_tarski(X5,X7),X3)
                | ~ m1_subset_1(X7,X1) )
            | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
          & ( ? [X8] :
                ( r2_hidden(k4_tarski(X8,X6),X4)
                & r2_hidden(k4_tarski(X5,X8),X3)
                & m1_subset_1(X8,X1) )
            | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) )
     => ( ( ! [X7] :
              ( ~ r2_hidden(k4_tarski(X7,sK11),X4)
              | ~ r2_hidden(k4_tarski(sK10,X7),X3)
              | ~ m1_subset_1(X7,X1) )
          | ~ r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
        & ( ? [X8] :
              ( r2_hidden(k4_tarski(X8,sK11),X4)
              & r2_hidden(k4_tarski(sK10,X8),X3)
              & m1_subset_1(X8,X1) )
          | r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5,X6] :
              ( ( ! [X7] :
                    ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                    | ~ r2_hidden(k4_tarski(X5,X7),X3)
                    | ~ m1_subset_1(X7,X1) )
                | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
              & ( ? [X8] :
                    ( r2_hidden(k4_tarski(X8,X6),X4)
                    & r2_hidden(k4_tarski(X5,X8),X3)
                    & m1_subset_1(X8,X1) )
                | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ? [X6,X5] :
            ( ( ! [X7] :
                  ( ~ r2_hidden(k4_tarski(X7,X6),sK9)
                  | ~ r2_hidden(k4_tarski(X5,X7),X3)
                  | ~ m1_subset_1(X7,X1) )
              | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,sK9)) )
            & ( ? [X8] :
                  ( r2_hidden(k4_tarski(X8,X6),sK9)
                  & r2_hidden(k4_tarski(X5,X8),X3)
                  & m1_subset_1(X8,X1) )
              | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,sK9)) ) )
        & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5,X6] :
                  ( ( ! [X7] :
                        ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                        | ~ r2_hidden(k4_tarski(X5,X7),X3)
                        | ~ m1_subset_1(X7,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
                  & ( ? [X8] :
                        ( r2_hidden(k4_tarski(X8,X6),X4)
                        & r2_hidden(k4_tarski(X5,X8),X3)
                        & m1_subset_1(X8,X1) )
                    | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( ? [X4] :
            ( ? [X6,X5] :
                ( ( ! [X7] :
                      ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                      | ~ r2_hidden(k4_tarski(X5,X7),sK8)
                      | ~ m1_subset_1(X7,X1) )
                  | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,sK8,X4)) )
                & ( ? [X8] :
                      ( r2_hidden(k4_tarski(X8,X6),X4)
                      & r2_hidden(k4_tarski(X5,X8),sK8)
                      & m1_subset_1(X8,X1) )
                  | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,sK8,X4)) ) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5,X6] :
                      ( ( ! [X7] :
                            ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                            | ~ r2_hidden(k4_tarski(X5,X7),X3)
                            | ~ m1_subset_1(X7,X1) )
                        | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
                      & ( ? [X8] :
                            ( r2_hidden(k4_tarski(X8,X6),X4)
                            & r2_hidden(k4_tarski(X5,X8),X3)
                            & m1_subset_1(X8,X1) )
                        | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X6,X5] :
                    ( ( ! [X7] :
                          ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                          | ~ r2_hidden(k4_tarski(X5,X7),X3)
                          | ~ m1_subset_1(X7,X1) )
                      | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,sK7,X3,X4)) )
                    & ( ? [X8] :
                          ( r2_hidden(k4_tarski(X8,X6),X4)
                          & r2_hidden(k4_tarski(X5,X8),X3)
                          & m1_subset_1(X8,X1) )
                      | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,sK7,X3,X4)) ) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,sK7))) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
        & ~ v1_xboole_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5,X6] :
                          ( ( ! [X7] :
                                ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                                | ~ r2_hidden(k4_tarski(X5,X7),X3)
                                | ~ m1_subset_1(X7,X1) )
                            | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
                          & ( ? [X8] :
                                ( r2_hidden(k4_tarski(X8,X6),X4)
                                & r2_hidden(k4_tarski(X5,X8),X3)
                                & m1_subset_1(X8,X1) )
                            | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X6,X5] :
                        ( ( ! [X7] :
                              ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                              | ~ r2_hidden(k4_tarski(X5,X7),X3)
                              | ~ m1_subset_1(X7,sK6) )
                          | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,sK6,sK6,X2,X3,X4)) )
                        & ( ? [X8] :
                              ( r2_hidden(k4_tarski(X8,X6),X4)
                              & r2_hidden(k4_tarski(X5,X8),X3)
                              & m1_subset_1(X8,sK6) )
                          | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,sK6,sK6,X2,X3,X4)) ) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,X2))) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,sK6))) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5,X6] :
                            ( ( ! [X7] :
                                  ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                                  | ~ r2_hidden(k4_tarski(X5,X7),X3)
                                  | ~ m1_subset_1(X7,X1) )
                              | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
                            & ( ? [X8] :
                                  ( r2_hidden(k4_tarski(X8,X6),X4)
                                  & r2_hidden(k4_tarski(X5,X8),X3)
                                  & m1_subset_1(X8,X1) )
                              | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
                & ~ v1_xboole_0(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X6,X5] :
                          ( ( ! [X7] :
                                ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                                | ~ r2_hidden(k4_tarski(X5,X7),X3)
                                | ~ m1_subset_1(X7,X1) )
                            | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK5,X1,X1,X2,X3,X4)) )
                          & ( ? [X8] :
                                ( r2_hidden(k4_tarski(X8,X6),X4)
                                & r2_hidden(k4_tarski(X5,X8),X3)
                                & m1_subset_1(X8,X1) )
                            | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK5,X1,X1,X2,X3,X4)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ! [X7] :
          ( ~ r2_hidden(k4_tarski(X7,sK11),sK9)
          | ~ r2_hidden(k4_tarski(sK10,X7),sK8)
          | ~ m1_subset_1(X7,sK6) )
      | ~ r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9)) )
    & ( ( r2_hidden(k4_tarski(sK12,sK11),sK9)
        & r2_hidden(k4_tarski(sK10,sK12),sK8)
        & m1_subset_1(sK12,sK6) )
      | r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9)) )
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & ~ v1_xboole_0(sK7)
    & ~ v1_xboole_0(sK6)
    & ~ v1_xboole_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9,sK10,sK11,sK12])],[f37,f44,f43,f42,f41,f40,f39,f38])).

fof(f66,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,
    ( r2_hidden(k4_tarski(sK12,sK11),sK9)
    | r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9)) ),
    inference(cnf_transformation,[],[f45])).

fof(f48,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f34])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f4,f32])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f71,plain,(
    ! [X7] :
      ( ~ r2_hidden(k4_tarski(X7,sK11),sK9)
      | ~ r2_hidden(k4_tarski(sK10,X7),sK8)
      | ~ m1_subset_1(X7,sK6)
      | ~ r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,
    ( r2_hidden(k4_tarski(sK10,sK12),sK8)
    | r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9)) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,
    ( m1_subset_1(sK12,sK6)
    | r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_350,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_102939,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9))
    | k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9) != X1
    | k4_tarski(sK10,sK11) != X0 ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_103045,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9))
    | k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9) != X2
    | k4_tarski(sK10,sK11) != k4_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_102939])).

cnf(c_103669,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK8,sK9))
    | r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9))
    | k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9) != k5_relat_1(sK8,sK9)
    | k4_tarski(sK10,sK11) != k4_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_103045])).

cnf(c_117767,plain,
    ( r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9))
    | ~ r2_hidden(k4_tarski(sK10,sK11),k5_relat_1(sK8,sK9))
    | k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9) != k5_relat_1(sK8,sK9)
    | k4_tarski(sK10,sK11) != k4_tarski(sK10,sK11) ),
    inference(instantiation,[status(thm)],[c_103669])).

cnf(c_4,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_10294,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | r2_hidden(k4_tarski(X0,X3),k5_relat_1(X2,sK9))
    | ~ r2_hidden(k4_tarski(X1,X3),sK9)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,sK9))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_34833,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK8,sK9))
    | ~ r2_hidden(k4_tarski(X0,X2),sK8)
    | ~ r2_hidden(k4_tarski(X2,X1),sK9)
    | ~ v1_relat_1(k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_10294])).

cnf(c_61712,plain,
    ( ~ r2_hidden(k4_tarski(sK12,X0),sK9)
    | r2_hidden(k4_tarski(sK10,X0),k5_relat_1(sK8,sK9))
    | ~ r2_hidden(k4_tarski(sK10,sK12),sK8)
    | ~ v1_relat_1(k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_34833])).

cnf(c_93615,plain,
    ( ~ r2_hidden(k4_tarski(sK12,sK11),sK9)
    | ~ r2_hidden(k4_tarski(sK10,sK12),sK8)
    | r2_hidden(k4_tarski(sK10,sK11),k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_61712])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_11030,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k5_relat_1(X0,sK9))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_30908,plain,
    ( v1_relat_1(k5_relat_1(sK8,sK9))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_11030])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_777,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_778,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_790,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2892,plain,
    ( k4_relset_1(X0,X1,sK6,sK7,X2,sK9) = k5_relat_1(X2,sK9)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_778,c_790])).

cnf(c_3058,plain,
    ( k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9) = k5_relat_1(sK8,sK9) ),
    inference(superposition,[status(thm)],[c_777,c_2892])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(k4_tarski(sK12,sK11),sK9)
    | r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_781,plain,
    ( r2_hidden(k4_tarski(sK12,sK11),sK9) = iProver_top
    | r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3101,plain,
    ( r2_hidden(k4_tarski(sK12,sK11),sK9) = iProver_top
    | r2_hidden(k4_tarski(sK10,sK11),k5_relat_1(sK8,sK9)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3058,c_781])).

cnf(c_5,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK3(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_794,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X2,X3,X0,X1),X1),X3) = iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_784,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2140,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | m1_subset_1(X0,k2_zfmisc_1(sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_778,c_784])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_785,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2530,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK6,sK7)) = iProver_top
    | r2_hidden(X0,sK9) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2140,c_785])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_787,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2870,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK9) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2530,c_787])).

cnf(c_4632,plain,
    ( r2_hidden(sK3(X0,sK9,X1,X2),sK6) = iProver_top
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK9)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK6,sK7)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(X0,sK9)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_794,c_2870])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27,plain,
    ( v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_28,plain,
    ( v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_8,plain,
    ( m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_57,plain,
    ( m1_subset_1(sK4(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_59,plain,
    ( m1_subset_1(sK4(sK6),sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_841,plain,
    ( r2_hidden(X0,sK7)
    | ~ m1_subset_1(X0,sK7)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_910,plain,
    ( r2_hidden(sK4(sK7),sK7)
    | ~ m1_subset_1(sK4(sK7),sK7)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_911,plain,
    ( r2_hidden(sK4(sK7),sK7) = iProver_top
    | m1_subset_1(sK4(sK7),sK7) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_910])).

cnf(c_847,plain,
    ( r2_hidden(X0,sK6)
    | ~ m1_subset_1(X0,sK6)
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_928,plain,
    ( r2_hidden(sK4(sK6),sK6)
    | ~ m1_subset_1(sK4(sK6),sK6)
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_847])).

cnf(c_929,plain,
    ( r2_hidden(sK4(sK6),sK6) = iProver_top
    | m1_subset_1(sK4(sK6),sK6) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_928])).

cnf(c_1047,plain,
    ( m1_subset_1(sK4(sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1048,plain,
    ( m1_subset_1(sK4(sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1047])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_799,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1758,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_778,c_799])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1378,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,sK6)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(sK6,X1)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2196,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK4(sK6),X0),k2_zfmisc_1(sK6,X1))
    | ~ r2_hidden(sK4(sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_3182,plain,
    ( r2_hidden(k4_tarski(sK4(sK6),sK4(sK7)),k2_zfmisc_1(sK6,sK7))
    | ~ r2_hidden(sK4(sK7),sK7)
    | ~ r2_hidden(sK4(sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_2196])).

cnf(c_3183,plain,
    ( r2_hidden(k4_tarski(sK4(sK6),sK4(sK7)),k2_zfmisc_1(sK6,sK7)) = iProver_top
    | r2_hidden(sK4(sK7),sK7) != iProver_top
    | r2_hidden(sK4(sK6),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3182])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_6065,plain,
    ( ~ r2_hidden(k4_tarski(sK4(sK6),sK4(sK7)),k2_zfmisc_1(sK6,sK7))
    | ~ v1_xboole_0(k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6066,plain,
    ( r2_hidden(k4_tarski(sK4(sK6),sK4(sK7)),k2_zfmisc_1(sK6,sK7)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6065])).

cnf(c_11031,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(X0,sK9)) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11030])).

cnf(c_25361,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK9)) != iProver_top
    | r2_hidden(sK3(X0,sK9,X1,X2),sK6) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4632,c_27,c_28,c_59,c_911,c_929,c_1048,c_1758,c_3183,c_6066,c_11031])).

cnf(c_25362,plain,
    ( r2_hidden(sK3(X0,sK9,X1,X2),sK6) = iProver_top
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK9)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_25361])).

cnf(c_25384,plain,
    ( r2_hidden(sK3(sK8,sK9,sK10,sK11),sK6) = iProver_top
    | r2_hidden(k4_tarski(sK12,sK11),sK9) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3101,c_25362])).

cnf(c_1759,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_777,c_799])).

cnf(c_25963,plain,
    ( r2_hidden(k4_tarski(sK12,sK11),sK9) = iProver_top
    | r2_hidden(sK3(sK8,sK9,sK10,sK11),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25384,c_1759])).

cnf(c_25964,plain,
    ( r2_hidden(sK3(sK8,sK9,sK10,sK11),sK6) = iProver_top
    | r2_hidden(k4_tarski(sK12,sK11),sK9) = iProver_top ),
    inference(renaming,[status(thm)],[c_25963])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_786,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_25967,plain,
    ( r2_hidden(k4_tarski(sK12,sK11),sK9) = iProver_top
    | m1_subset_1(sK3(sK8,sK9,sK10,sK11),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_25964,c_786])).

cnf(c_6,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK3(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_793,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(X2,X3,X0,X1)),X2) = iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X0,sK11),sK9)
    | ~ r2_hidden(k4_tarski(sK10,X0),sK8)
    | ~ r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9))
    | ~ m1_subset_1(X0,sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_782,plain,
    ( r2_hidden(k4_tarski(X0,sK11),sK9) != iProver_top
    | r2_hidden(k4_tarski(sK10,X0),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9)) != iProver_top
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1469,plain,
    ( r2_hidden(k4_tarski(X0,sK11),sK9) != iProver_top
    | r2_hidden(k4_tarski(sK12,sK11),sK9) = iProver_top
    | r2_hidden(k4_tarski(sK10,X0),sK8) != iProver_top
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_781,c_782])).

cnf(c_2998,plain,
    ( r2_hidden(k4_tarski(X0,sK11),k5_relat_1(X1,sK9)) != iProver_top
    | r2_hidden(k4_tarski(sK12,sK11),sK9) = iProver_top
    | r2_hidden(k4_tarski(sK10,sK3(X1,sK9,X0,sK11)),sK8) != iProver_top
    | m1_subset_1(sK3(X1,sK9,X0,sK11),sK6) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,sK9)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_794,c_1469])).

cnf(c_4263,plain,
    ( v1_relat_1(k5_relat_1(X1,sK9)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | m1_subset_1(sK3(X1,sK9,X0,sK11),sK6) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK3(X1,sK9,X0,sK11)),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK12,sK11),sK9) = iProver_top
    | r2_hidden(k4_tarski(X0,sK11),k5_relat_1(X1,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2998,c_1758])).

cnf(c_4264,plain,
    ( r2_hidden(k4_tarski(X0,sK11),k5_relat_1(X1,sK9)) != iProver_top
    | r2_hidden(k4_tarski(sK12,sK11),sK9) = iProver_top
    | r2_hidden(k4_tarski(sK10,sK3(X1,sK9,X0,sK11)),sK8) != iProver_top
    | m1_subset_1(sK3(X1,sK9,X0,sK11),sK6) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4263])).

cnf(c_4269,plain,
    ( r2_hidden(k4_tarski(sK12,sK11),sK9) = iProver_top
    | r2_hidden(k4_tarski(sK10,sK11),k5_relat_1(sK8,sK9)) != iProver_top
    | m1_subset_1(sK3(sK8,sK9,sK10,sK11),sK6) != iProver_top
    | v1_relat_1(k5_relat_1(sK8,sK9)) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_793,c_4264])).

cnf(c_5437,plain,
    ( r2_hidden(k4_tarski(sK12,sK11),sK9) = iProver_top
    | m1_subset_1(sK3(sK8,sK9,sK10,sK11),sK6) != iProver_top
    | v1_relat_1(k5_relat_1(sK8,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4269,c_1758,c_1759,c_3101])).

cnf(c_26849,plain,
    ( r2_hidden(k4_tarski(sK12,sK11),sK9) = iProver_top
    | v1_relat_1(k5_relat_1(sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_25967,c_5437])).

cnf(c_26851,plain,
    ( r2_hidden(k4_tarski(sK12,sK11),sK9)
    | ~ v1_relat_1(k5_relat_1(sK8,sK9)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_26849])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(k4_tarski(sK10,sK12),sK8)
    | r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_780,plain,
    ( r2_hidden(k4_tarski(sK10,sK12),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3102,plain,
    ( r2_hidden(k4_tarski(sK10,sK12),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK10,sK11),k5_relat_1(sK8,sK9)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3058,c_780])).

cnf(c_25383,plain,
    ( r2_hidden(sK3(sK8,sK9,sK10,sK11),sK6) = iProver_top
    | r2_hidden(k4_tarski(sK10,sK12),sK8) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3102,c_25362])).

cnf(c_25955,plain,
    ( r2_hidden(k4_tarski(sK10,sK12),sK8) = iProver_top
    | r2_hidden(sK3(sK8,sK9,sK10,sK11),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25383,c_1759])).

cnf(c_25956,plain,
    ( r2_hidden(sK3(sK8,sK9,sK10,sK11),sK6) = iProver_top
    | r2_hidden(k4_tarski(sK10,sK12),sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_25955])).

cnf(c_25959,plain,
    ( r2_hidden(k4_tarski(sK10,sK12),sK8) = iProver_top
    | m1_subset_1(sK3(sK8,sK9,sK10,sK11),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_25956,c_786])).

cnf(c_1274,plain,
    ( r2_hidden(k4_tarski(X0,sK11),sK9) != iProver_top
    | r2_hidden(k4_tarski(sK10,X0),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK12),sK8) = iProver_top
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_780,c_782])).

cnf(c_2999,plain,
    ( r2_hidden(k4_tarski(X0,sK11),k5_relat_1(X1,sK9)) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK3(X1,sK9,X0,sK11)),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK12),sK8) = iProver_top
    | m1_subset_1(sK3(X1,sK9,X0,sK11),sK6) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,sK9)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_794,c_1274])).

cnf(c_4274,plain,
    ( v1_relat_1(k5_relat_1(X1,sK9)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | m1_subset_1(sK3(X1,sK9,X0,sK11),sK6) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK12),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK10,sK3(X1,sK9,X0,sK11)),sK8) != iProver_top
    | r2_hidden(k4_tarski(X0,sK11),k5_relat_1(X1,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2999,c_1758])).

cnf(c_4275,plain,
    ( r2_hidden(k4_tarski(X0,sK11),k5_relat_1(X1,sK9)) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK3(X1,sK9,X0,sK11)),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK12),sK8) = iProver_top
    | m1_subset_1(sK3(X1,sK9,X0,sK11),sK6) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4274])).

cnf(c_4280,plain,
    ( r2_hidden(k4_tarski(sK10,sK12),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK10,sK11),k5_relat_1(sK8,sK9)) != iProver_top
    | m1_subset_1(sK3(sK8,sK9,sK10,sK11),sK6) != iProver_top
    | v1_relat_1(k5_relat_1(sK8,sK9)) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_793,c_4275])).

cnf(c_5497,plain,
    ( r2_hidden(k4_tarski(sK10,sK12),sK8) = iProver_top
    | m1_subset_1(sK3(sK8,sK9,sK10,sK11),sK6) != iProver_top
    | v1_relat_1(k5_relat_1(sK8,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4280,c_1758,c_1759,c_3102])).

cnf(c_26842,plain,
    ( r2_hidden(k4_tarski(sK10,sK12),sK8) = iProver_top
    | v1_relat_1(k5_relat_1(sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_25959,c_5497])).

cnf(c_26845,plain,
    ( r2_hidden(k4_tarski(sK10,sK12),sK8)
    | ~ v1_relat_1(k5_relat_1(sK8,sK9)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_26842])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9))
    | m1_subset_1(sK12,sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_779,plain,
    ( r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9)) = iProver_top
    | m1_subset_1(sK12,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3103,plain,
    ( r2_hidden(k4_tarski(sK10,sK11),k5_relat_1(sK8,sK9)) = iProver_top
    | m1_subset_1(sK12,sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3058,c_779])).

cnf(c_25385,plain,
    ( r2_hidden(sK3(sK8,sK9,sK10,sK11),sK6) = iProver_top
    | m1_subset_1(sK12,sK6) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3103,c_25362])).

cnf(c_25770,plain,
    ( m1_subset_1(sK12,sK6) = iProver_top
    | r2_hidden(sK3(sK8,sK9,sK10,sK11),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25385,c_1759])).

cnf(c_25771,plain,
    ( r2_hidden(sK3(sK8,sK9,sK10,sK11),sK6) = iProver_top
    | m1_subset_1(sK12,sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_25770])).

cnf(c_25774,plain,
    ( m1_subset_1(sK3(sK8,sK9,sK10,sK11),sK6) = iProver_top
    | m1_subset_1(sK12,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_25771,c_786])).

cnf(c_1269,plain,
    ( r2_hidden(k4_tarski(X0,sK11),sK9) != iProver_top
    | r2_hidden(k4_tarski(sK10,X0),sK8) != iProver_top
    | m1_subset_1(X0,sK6) != iProver_top
    | m1_subset_1(sK12,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_779,c_782])).

cnf(c_3000,plain,
    ( r2_hidden(k4_tarski(X0,sK11),k5_relat_1(X1,sK9)) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK3(X1,sK9,X0,sK11)),sK8) != iProver_top
    | m1_subset_1(sK3(X1,sK9,X0,sK11),sK6) != iProver_top
    | m1_subset_1(sK12,sK6) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,sK9)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_794,c_1269])).

cnf(c_4254,plain,
    ( v1_relat_1(k5_relat_1(X1,sK9)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | m1_subset_1(sK12,sK6) = iProver_top
    | m1_subset_1(sK3(X1,sK9,X0,sK11),sK6) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK3(X1,sK9,X0,sK11)),sK8) != iProver_top
    | r2_hidden(k4_tarski(X0,sK11),k5_relat_1(X1,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3000,c_1758])).

cnf(c_4255,plain,
    ( r2_hidden(k4_tarski(X0,sK11),k5_relat_1(X1,sK9)) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK3(X1,sK9,X0,sK11)),sK8) != iProver_top
    | m1_subset_1(sK3(X1,sK9,X0,sK11),sK6) != iProver_top
    | m1_subset_1(sK12,sK6) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4254])).

cnf(c_4260,plain,
    ( r2_hidden(k4_tarski(sK10,sK11),k5_relat_1(sK8,sK9)) != iProver_top
    | m1_subset_1(sK3(sK8,sK9,sK10,sK11),sK6) != iProver_top
    | m1_subset_1(sK12,sK6) = iProver_top
    | v1_relat_1(k5_relat_1(sK8,sK9)) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_793,c_4255])).

cnf(c_5283,plain,
    ( m1_subset_1(sK3(sK8,sK9,sK10,sK11),sK6) != iProver_top
    | m1_subset_1(sK12,sK6) = iProver_top
    | v1_relat_1(k5_relat_1(sK8,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4260,c_1758,c_1759,c_3103])).

cnf(c_26377,plain,
    ( m1_subset_1(sK12,sK6) = iProver_top
    | v1_relat_1(k5_relat_1(sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_25774,c_5283])).

cnf(c_26378,plain,
    ( m1_subset_1(sK12,sK6)
    | ~ v1_relat_1(k5_relat_1(sK8,sK9)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_26377])).

cnf(c_343,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_12878,plain,
    ( k4_tarski(sK10,sK11) = k4_tarski(sK10,sK11) ),
    inference(instantiation,[status(thm)],[c_343])).

cnf(c_1805,plain,
    ( ~ r2_hidden(k4_tarski(sK12,sK11),sK9)
    | ~ r2_hidden(k4_tarski(sK10,sK12),sK8)
    | ~ r2_hidden(k4_tarski(sK10,sK11),k4_relset_1(sK5,sK6,sK6,sK7,sK8,sK9))
    | ~ m1_subset_1(sK12,sK6) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1764,plain,
    ( v1_relat_1(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1759])).

cnf(c_1763,plain,
    ( v1_relat_1(sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1758])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_117767,c_93615,c_30908,c_26851,c_26845,c_26378,c_12878,c_3058,c_1805,c_1764,c_1763])).


%------------------------------------------------------------------------------

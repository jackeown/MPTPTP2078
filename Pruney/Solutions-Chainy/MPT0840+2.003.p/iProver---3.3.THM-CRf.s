%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:58 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :  147 (2300 expanded)
%              Number of clauses        :   93 ( 651 expanded)
%              Number of leaves         :   16 ( 662 expanded)
%              Depth                    :   30
%              Number of atoms          :  639 (15884 expanded)
%              Number of equality atoms :  290 (1315 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
           => ! [X5,X6] :
                ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
              <=> ? [X7] :
                    ( r2_hidden(k4_tarski(X7,X6),X4)
                    & r2_hidden(k4_tarski(X5,X7),X3)
                    & m1_subset_1(X7,X1) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5,X6] :
              ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
            <~> ? [X7] :
                  ( r2_hidden(k4_tarski(X7,X6),X4)
                  & r2_hidden(k4_tarski(X5,X7),X3)
                  & m1_subset_1(X7,X1) ) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
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
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
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
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f29])).

fof(f34,plain,(
    ! [X6,X4,X5,X3,X1] :
      ( ? [X8] :
          ( r2_hidden(k4_tarski(X8,X6),X4)
          & r2_hidden(k4_tarski(X5,X8),X3)
          & m1_subset_1(X8,X1) )
     => ( r2_hidden(k4_tarski(sK11,X6),X4)
        & r2_hidden(k4_tarski(X5,sK11),X3)
        & m1_subset_1(sK11,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
              ( ~ r2_hidden(k4_tarski(X7,sK10),X4)
              | ~ r2_hidden(k4_tarski(sK9,X7),X3)
              | ~ m1_subset_1(X7,X1) )
          | ~ r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
        & ( ? [X8] :
              ( r2_hidden(k4_tarski(X8,sK10),X4)
              & r2_hidden(k4_tarski(sK9,X8),X3)
              & m1_subset_1(X8,X1) )
          | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
                  ( ~ r2_hidden(k4_tarski(X7,X6),sK8)
                  | ~ r2_hidden(k4_tarski(X5,X7),X3)
                  | ~ m1_subset_1(X7,X1) )
              | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,sK8)) )
            & ( ? [X8] :
                  ( r2_hidden(k4_tarski(X8,X6),sK8)
                  & r2_hidden(k4_tarski(X5,X8),X3)
                  & m1_subset_1(X8,X1) )
              | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,sK8)) ) )
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
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
                    | ~ r2_hidden(k4_tarski(X5,X7),sK7)
                    | ~ m1_subset_1(X7,sK5) )
                | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK4,sK5,sK5,sK6,sK7,X4)) )
              & ( ? [X8] :
                    ( r2_hidden(k4_tarski(X8,X6),X4)
                    & r2_hidden(k4_tarski(X5,X8),sK7)
                    & m1_subset_1(X8,sK5) )
                | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK4,sK5,sK5,sK6,sK7,X4)) ) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( ! [X7] :
          ( ~ r2_hidden(k4_tarski(X7,sK10),sK8)
          | ~ r2_hidden(k4_tarski(sK9,X7),sK7)
          | ~ m1_subset_1(X7,sK5) )
      | ~ r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) )
    & ( ( r2_hidden(k4_tarski(sK11,sK10),sK8)
        & r2_hidden(k4_tarski(sK9,sK11),sK7)
        & m1_subset_1(sK11,sK5) )
      | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) )
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10,sK11])],[f30,f34,f33,f32,f31])).

fof(f51,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,
    ( r2_hidden(k4_tarski(sK9,sK11),sK7)
    | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f27,f26,f25])).

fof(f43,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f21])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f42,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f56,plain,(
    ! [X7] :
      ( ~ r2_hidden(k4_tarski(X7,sK10),sK8)
      | ~ r2_hidden(k4_tarski(sK9,X7),sK7)
      | ~ m1_subset_1(X7,sK5)
      | ~ r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,
    ( m1_subset_1(sK11,sK5)
    | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,
    ( r2_hidden(k4_tarski(sK11,sK10),sK8)
    | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_585,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_577,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_578,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_583,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1203,plain,
    ( k4_relset_1(X0,X1,sK5,sK6,X2,sK8) = k5_relat_1(X2,sK8)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_583])).

cnf(c_1469,plain,
    ( k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8) = k5_relat_1(sK7,sK8) ),
    inference(superposition,[status(thm)],[c_577,c_1203])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(k4_tarski(sK9,sK11),sK7)
    | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_580,plain,
    ( r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
    | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1488,plain,
    ( r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
    | r2_hidden(k4_tarski(sK9,sK10),k5_relat_1(sK7,sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1469,c_580])).

cnf(c_10,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK3(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_587,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X2,X3,X0,X1),X1),X3) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_594,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1746,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK5,sK6)) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_594])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_595,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1895,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1746,c_595])).

cnf(c_2773,plain,
    ( r2_hidden(sK3(X0,sK8,X1,X2),sK5) = iProver_top
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK8)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_587,c_1895])).

cnf(c_13,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_584,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_592,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1714,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_592])).

cnf(c_1821,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_584,c_1714])).

cnf(c_5166,plain,
    ( v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK8)) != iProver_top
    | r2_hidden(sK3(X0,sK8,X1,X2),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2773,c_1821])).

cnf(c_5167,plain,
    ( r2_hidden(sK3(X0,sK8,X1,X2),sK5) = iProver_top
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK8)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5166])).

cnf(c_5178,plain,
    ( r2_hidden(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
    | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1488,c_5167])).

cnf(c_1715,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_577,c_592])).

cnf(c_1824,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_584,c_1715])).

cnf(c_5268,plain,
    ( v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
    | r2_hidden(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5178,c_1824])).

cnf(c_5269,plain,
    ( r2_hidden(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
    | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5268])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_593,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5272,plain,
    ( m1_subset_1(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
    | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5269,c_593])).

cnf(c_9,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_588,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X3,X0),X4) != iProver_top
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X4) != iProver_top
    | v1_relat_1(k5_relat_1(X4,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2545,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X0,X3),k5_relat_1(X2,k2_zfmisc_1(sK5,sK6))) = iProver_top
    | r2_hidden(k4_tarski(X1,X3),sK8) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k5_relat_1(X2,k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1746,c_588])).

cnf(c_2911,plain,
    ( r2_hidden(k4_tarski(sK9,X0),k5_relat_1(k5_relat_1(sK7,sK8),k2_zfmisc_1(sK5,sK6))) = iProver_top
    | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
    | r2_hidden(k4_tarski(sK10,X0),sK8) != iProver_top
    | v1_relat_1(k5_relat_1(k5_relat_1(sK7,sK8),k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1488,c_2545])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK3(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_586,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(X2,X3,X0,X1)),X2) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_15,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(k4_tarski(X0,sK10),sK8)
    | ~ r2_hidden(k4_tarski(sK9,X0),sK7)
    | ~ r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_582,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK10),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK9,X0),sK7) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1004,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK10),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK9,X0),sK7) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_580,c_582])).

cnf(c_1947,plain,
    ( m1_subset_1(sK3(X0,sK8,X1,sK10),sK5) != iProver_top
    | r2_hidden(k4_tarski(X1,sK10),k5_relat_1(X0,sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK3(X0,sK8,X1,sK10)),sK7) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_587,c_1004])).

cnf(c_3323,plain,
    ( v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
    | r2_hidden(k4_tarski(sK9,sK3(X0,sK8,X1,sK10)),sK7) != iProver_top
    | r2_hidden(k4_tarski(X1,sK10),k5_relat_1(X0,sK8)) != iProver_top
    | m1_subset_1(sK3(X0,sK8,X1,sK10),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1947,c_1821])).

cnf(c_3324,plain,
    ( m1_subset_1(sK3(X0,sK8,X1,sK10),sK5) != iProver_top
    | r2_hidden(k4_tarski(X1,sK10),k5_relat_1(X0,sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK3(X0,sK8,X1,sK10)),sK7) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3323])).

cnf(c_3329,plain,
    ( m1_subset_1(sK3(sK7,sK8,sK9,sK10),sK5) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
    | r2_hidden(k4_tarski(sK9,sK10),k5_relat_1(sK7,sK8)) != iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_586,c_3324])).

cnf(c_5282,plain,
    ( v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2911,c_1488,c_1821,c_1824,c_3329,c_5272])).

cnf(c_5283,plain,
    ( r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5282])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK11,sK5)
    | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_579,plain,
    ( m1_subset_1(sK11,sK5) = iProver_top
    | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1489,plain,
    ( m1_subset_1(sK11,sK5) = iProver_top
    | r2_hidden(k4_tarski(sK9,sK10),k5_relat_1(sK7,sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1469,c_579])).

cnf(c_5180,plain,
    ( m1_subset_1(sK11,sK5) = iProver_top
    | r2_hidden(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1489,c_5167])).

cnf(c_5261,plain,
    ( v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
    | r2_hidden(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
    | m1_subset_1(sK11,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5180,c_1824])).

cnf(c_5262,plain,
    ( m1_subset_1(sK11,sK5) = iProver_top
    | r2_hidden(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5261])).

cnf(c_5265,plain,
    ( m1_subset_1(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
    | m1_subset_1(sK11,sK5) = iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5262,c_593])).

cnf(c_864,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | m1_subset_1(sK11,sK5) = iProver_top
    | r2_hidden(k4_tarski(X0,sK10),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK9,X0),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_579,c_582])).

cnf(c_1948,plain,
    ( m1_subset_1(sK3(X0,sK8,X1,sK10),sK5) != iProver_top
    | m1_subset_1(sK11,sK5) = iProver_top
    | r2_hidden(k4_tarski(X1,sK10),k5_relat_1(X0,sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK3(X0,sK8,X1,sK10)),sK7) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_587,c_864])).

cnf(c_3128,plain,
    ( v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK3(X0,sK8,X1,sK10)),sK7) != iProver_top
    | r2_hidden(k4_tarski(X1,sK10),k5_relat_1(X0,sK8)) != iProver_top
    | m1_subset_1(sK11,sK5) = iProver_top
    | m1_subset_1(sK3(X0,sK8,X1,sK10),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1948,c_1821])).

cnf(c_3129,plain,
    ( m1_subset_1(sK3(X0,sK8,X1,sK10),sK5) != iProver_top
    | m1_subset_1(sK11,sK5) = iProver_top
    | r2_hidden(k4_tarski(X1,sK10),k5_relat_1(X0,sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK3(X0,sK8,X1,sK10)),sK7) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3128])).

cnf(c_3134,plain,
    ( m1_subset_1(sK3(sK7,sK8,sK9,sK10),sK5) != iProver_top
    | m1_subset_1(sK11,sK5) = iProver_top
    | r2_hidden(k4_tarski(sK9,sK10),k5_relat_1(sK7,sK8)) != iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_586,c_3129])).

cnf(c_5403,plain,
    ( m1_subset_1(sK11,sK5) = iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5265,c_1489,c_1821,c_1824,c_3134])).

cnf(c_5407,plain,
    ( m1_subset_1(sK11,sK5) = iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_585,c_5403])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(k4_tarski(sK11,sK10),sK8)
    | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_581,plain,
    ( r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1487,plain,
    ( r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK9,sK10),k5_relat_1(sK7,sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1469,c_581])).

cnf(c_2912,plain,
    ( r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK9,X0),k5_relat_1(k5_relat_1(sK7,sK8),k2_zfmisc_1(sK5,sK6))) = iProver_top
    | r2_hidden(k4_tarski(sK10,X0),sK8) != iProver_top
    | v1_relat_1(k5_relat_1(k5_relat_1(sK7,sK8),k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_2545])).

cnf(c_1009,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK10),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK9,X0),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_581,c_582])).

cnf(c_1946,plain,
    ( m1_subset_1(sK3(X0,sK8,X1,sK10),sK5) != iProver_top
    | r2_hidden(k4_tarski(X1,sK10),k5_relat_1(X0,sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK9,sK3(X0,sK8,X1,sK10)),sK7) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_587,c_1009])).

cnf(c_3174,plain,
    ( v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK3(X0,sK8,X1,sK10)),sK7) != iProver_top
    | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
    | r2_hidden(k4_tarski(X1,sK10),k5_relat_1(X0,sK8)) != iProver_top
    | m1_subset_1(sK3(X0,sK8,X1,sK10),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1946,c_1821])).

cnf(c_3175,plain,
    ( m1_subset_1(sK3(X0,sK8,X1,sK10),sK5) != iProver_top
    | r2_hidden(k4_tarski(X1,sK10),k5_relat_1(X0,sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK9,sK3(X0,sK8,X1,sK10)),sK7) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3174])).

cnf(c_3180,plain,
    ( m1_subset_1(sK3(sK7,sK8,sK9,sK10),sK5) != iProver_top
    | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK9,sK10),k5_relat_1(sK7,sK8)) != iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_586,c_3175])).

cnf(c_5179,plain,
    ( r2_hidden(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
    | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_5167])).

cnf(c_5275,plain,
    ( v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
    | r2_hidden(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5179,c_1824])).

cnf(c_5276,plain,
    ( r2_hidden(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
    | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5275])).

cnf(c_5279,plain,
    ( m1_subset_1(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
    | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5276,c_593])).

cnf(c_5308,plain,
    ( v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2912,c_1487,c_1821,c_1824,c_3180,c_5279])).

cnf(c_5309,plain,
    ( r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5308])).

cnf(c_5315,plain,
    ( r2_hidden(k4_tarski(X0,sK11),X1) != iProver_top
    | r2_hidden(k4_tarski(X0,sK10),k5_relat_1(X1,sK8)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,sK8)) != iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5309,c_588])).

cnf(c_5565,plain,
    ( v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
    | v1_relat_1(k5_relat_1(X1,sK8)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | r2_hidden(k4_tarski(X0,sK10),k5_relat_1(X1,sK8)) = iProver_top
    | r2_hidden(k4_tarski(X0,sK11),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5315,c_1821])).

cnf(c_5566,plain,
    ( r2_hidden(k4_tarski(X0,sK11),X1) != iProver_top
    | r2_hidden(k4_tarski(X0,sK10),k5_relat_1(X1,sK8)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,sK8)) != iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5565])).

cnf(c_1490,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK10),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK9,X0),sK7) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK10),k5_relat_1(sK7,sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1469,c_582])).

cnf(c_5575,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK10),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK9,X0),sK7) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK11),sK7) != iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5566,c_1490])).

cnf(c_5620,plain,
    ( v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
    | m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK10),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK9,X0),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5575,c_1488,c_1821,c_1824,c_3329,c_5272])).

cnf(c_5621,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK10),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK9,X0),sK7) != iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5620])).

cnf(c_5627,plain,
    ( m1_subset_1(sK11,sK5) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK11),sK7) != iProver_top
    | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5309,c_5621])).

cnf(c_5678,plain,
    ( v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5272,c_1821,c_1824,c_5283,c_5407,c_5627])).

cnf(c_5682,plain,
    ( v1_relat_1(sK7) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_585,c_5678])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5682,c_1824,c_1821])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:05:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.58/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/0.98  
% 3.58/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.58/0.98  
% 3.58/0.98  ------  iProver source info
% 3.58/0.98  
% 3.58/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.58/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.58/0.98  git: non_committed_changes: false
% 3.58/0.98  git: last_make_outside_of_git: false
% 3.58/0.98  
% 3.58/0.98  ------ 
% 3.58/0.98  
% 3.58/0.98  ------ Input Options
% 3.58/0.98  
% 3.58/0.98  --out_options                           all
% 3.58/0.98  --tptp_safe_out                         true
% 3.58/0.98  --problem_path                          ""
% 3.58/0.98  --include_path                          ""
% 3.58/0.98  --clausifier                            res/vclausify_rel
% 3.58/0.98  --clausifier_options                    ""
% 3.58/0.98  --stdin                                 false
% 3.58/0.98  --stats_out                             all
% 3.58/0.98  
% 3.58/0.98  ------ General Options
% 3.58/0.98  
% 3.58/0.98  --fof                                   false
% 3.58/0.98  --time_out_real                         305.
% 3.58/0.98  --time_out_virtual                      -1.
% 3.58/0.98  --symbol_type_check                     false
% 3.58/0.98  --clausify_out                          false
% 3.58/0.98  --sig_cnt_out                           false
% 3.58/0.98  --trig_cnt_out                          false
% 3.58/0.98  --trig_cnt_out_tolerance                1.
% 3.58/0.98  --trig_cnt_out_sk_spl                   false
% 3.58/0.98  --abstr_cl_out                          false
% 3.58/0.98  
% 3.58/0.98  ------ Global Options
% 3.58/0.98  
% 3.58/0.98  --schedule                              default
% 3.58/0.98  --add_important_lit                     false
% 3.58/0.98  --prop_solver_per_cl                    1000
% 3.58/0.98  --min_unsat_core                        false
% 3.58/0.98  --soft_assumptions                      false
% 3.58/0.98  --soft_lemma_size                       3
% 3.58/0.98  --prop_impl_unit_size                   0
% 3.58/0.98  --prop_impl_unit                        []
% 3.58/0.98  --share_sel_clauses                     true
% 3.58/0.98  --reset_solvers                         false
% 3.58/0.98  --bc_imp_inh                            [conj_cone]
% 3.58/0.98  --conj_cone_tolerance                   3.
% 3.58/0.98  --extra_neg_conj                        none
% 3.58/0.98  --large_theory_mode                     true
% 3.58/0.98  --prolific_symb_bound                   200
% 3.58/0.98  --lt_threshold                          2000
% 3.58/0.98  --clause_weak_htbl                      true
% 3.58/0.98  --gc_record_bc_elim                     false
% 3.58/0.98  
% 3.58/0.98  ------ Preprocessing Options
% 3.58/0.98  
% 3.58/0.98  --preprocessing_flag                    true
% 3.58/0.98  --time_out_prep_mult                    0.1
% 3.58/0.98  --splitting_mode                        input
% 3.58/0.98  --splitting_grd                         true
% 3.58/0.98  --splitting_cvd                         false
% 3.58/0.98  --splitting_cvd_svl                     false
% 3.58/0.98  --splitting_nvd                         32
% 3.58/0.98  --sub_typing                            true
% 3.58/0.98  --prep_gs_sim                           true
% 3.58/0.98  --prep_unflatten                        true
% 3.58/0.98  --prep_res_sim                          true
% 3.58/0.98  --prep_upred                            true
% 3.58/0.98  --prep_sem_filter                       exhaustive
% 3.58/0.98  --prep_sem_filter_out                   false
% 3.58/0.98  --pred_elim                             true
% 3.58/0.98  --res_sim_input                         true
% 3.58/0.98  --eq_ax_congr_red                       true
% 3.58/0.98  --pure_diseq_elim                       true
% 3.58/0.98  --brand_transform                       false
% 3.58/0.98  --non_eq_to_eq                          false
% 3.58/0.98  --prep_def_merge                        true
% 3.58/0.98  --prep_def_merge_prop_impl              false
% 3.58/0.98  --prep_def_merge_mbd                    true
% 3.58/0.98  --prep_def_merge_tr_red                 false
% 3.58/0.98  --prep_def_merge_tr_cl                  false
% 3.58/0.98  --smt_preprocessing                     true
% 3.58/0.98  --smt_ac_axioms                         fast
% 3.58/0.98  --preprocessed_out                      false
% 3.58/0.98  --preprocessed_stats                    false
% 3.58/0.98  
% 3.58/0.98  ------ Abstraction refinement Options
% 3.58/0.98  
% 3.58/0.98  --abstr_ref                             []
% 3.58/0.98  --abstr_ref_prep                        false
% 3.58/0.98  --abstr_ref_until_sat                   false
% 3.58/0.98  --abstr_ref_sig_restrict                funpre
% 3.58/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.58/0.98  --abstr_ref_under                       []
% 3.58/0.98  
% 3.58/0.98  ------ SAT Options
% 3.58/0.98  
% 3.58/0.98  --sat_mode                              false
% 3.58/0.98  --sat_fm_restart_options                ""
% 3.58/0.98  --sat_gr_def                            false
% 3.58/0.98  --sat_epr_types                         true
% 3.58/0.98  --sat_non_cyclic_types                  false
% 3.58/0.98  --sat_finite_models                     false
% 3.58/0.98  --sat_fm_lemmas                         false
% 3.58/0.98  --sat_fm_prep                           false
% 3.58/0.98  --sat_fm_uc_incr                        true
% 3.58/0.98  --sat_out_model                         small
% 3.58/0.98  --sat_out_clauses                       false
% 3.58/0.98  
% 3.58/0.98  ------ QBF Options
% 3.58/0.98  
% 3.58/0.98  --qbf_mode                              false
% 3.58/0.98  --qbf_elim_univ                         false
% 3.58/0.98  --qbf_dom_inst                          none
% 3.58/0.98  --qbf_dom_pre_inst                      false
% 3.58/0.98  --qbf_sk_in                             false
% 3.58/0.98  --qbf_pred_elim                         true
% 3.58/0.98  --qbf_split                             512
% 3.58/0.98  
% 3.58/0.98  ------ BMC1 Options
% 3.58/0.98  
% 3.58/0.98  --bmc1_incremental                      false
% 3.58/0.98  --bmc1_axioms                           reachable_all
% 3.58/0.98  --bmc1_min_bound                        0
% 3.58/0.98  --bmc1_max_bound                        -1
% 3.58/0.98  --bmc1_max_bound_default                -1
% 3.58/0.98  --bmc1_symbol_reachability              true
% 3.58/0.98  --bmc1_property_lemmas                  false
% 3.58/0.98  --bmc1_k_induction                      false
% 3.58/0.98  --bmc1_non_equiv_states                 false
% 3.58/0.98  --bmc1_deadlock                         false
% 3.58/0.98  --bmc1_ucm                              false
% 3.58/0.98  --bmc1_add_unsat_core                   none
% 3.58/0.98  --bmc1_unsat_core_children              false
% 3.58/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.58/0.98  --bmc1_out_stat                         full
% 3.58/0.98  --bmc1_ground_init                      false
% 3.58/0.98  --bmc1_pre_inst_next_state              false
% 3.58/0.98  --bmc1_pre_inst_state                   false
% 3.58/0.98  --bmc1_pre_inst_reach_state             false
% 3.58/0.98  --bmc1_out_unsat_core                   false
% 3.58/0.98  --bmc1_aig_witness_out                  false
% 3.58/0.98  --bmc1_verbose                          false
% 3.58/0.98  --bmc1_dump_clauses_tptp                false
% 3.58/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.58/0.98  --bmc1_dump_file                        -
% 3.58/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.58/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.58/0.98  --bmc1_ucm_extend_mode                  1
% 3.58/0.98  --bmc1_ucm_init_mode                    2
% 3.58/0.98  --bmc1_ucm_cone_mode                    none
% 3.58/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.58/0.98  --bmc1_ucm_relax_model                  4
% 3.58/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.58/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.58/0.98  --bmc1_ucm_layered_model                none
% 3.58/0.98  --bmc1_ucm_max_lemma_size               10
% 3.58/0.98  
% 3.58/0.98  ------ AIG Options
% 3.58/0.98  
% 3.58/0.98  --aig_mode                              false
% 3.58/0.98  
% 3.58/0.98  ------ Instantiation Options
% 3.58/0.98  
% 3.58/0.98  --instantiation_flag                    true
% 3.58/0.98  --inst_sos_flag                         true
% 3.58/0.98  --inst_sos_phase                        true
% 3.58/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.58/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.58/0.98  --inst_lit_sel_side                     num_symb
% 3.58/0.98  --inst_solver_per_active                1400
% 3.58/0.98  --inst_solver_calls_frac                1.
% 3.58/0.98  --inst_passive_queue_type               priority_queues
% 3.58/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.58/0.98  --inst_passive_queues_freq              [25;2]
% 3.58/0.98  --inst_dismatching                      true
% 3.58/0.98  --inst_eager_unprocessed_to_passive     true
% 3.58/0.98  --inst_prop_sim_given                   true
% 3.58/0.98  --inst_prop_sim_new                     false
% 3.58/0.98  --inst_subs_new                         false
% 3.58/0.98  --inst_eq_res_simp                      false
% 3.58/0.98  --inst_subs_given                       false
% 3.58/0.98  --inst_orphan_elimination               true
% 3.58/0.98  --inst_learning_loop_flag               true
% 3.58/0.98  --inst_learning_start                   3000
% 3.58/0.98  --inst_learning_factor                  2
% 3.58/0.98  --inst_start_prop_sim_after_learn       3
% 3.58/0.98  --inst_sel_renew                        solver
% 3.58/0.98  --inst_lit_activity_flag                true
% 3.58/0.98  --inst_restr_to_given                   false
% 3.58/0.98  --inst_activity_threshold               500
% 3.58/0.98  --inst_out_proof                        true
% 3.58/0.98  
% 3.58/0.98  ------ Resolution Options
% 3.58/0.98  
% 3.58/0.98  --resolution_flag                       true
% 3.58/0.98  --res_lit_sel                           adaptive
% 3.58/0.98  --res_lit_sel_side                      none
% 3.58/0.98  --res_ordering                          kbo
% 3.58/0.98  --res_to_prop_solver                    active
% 3.58/0.98  --res_prop_simpl_new                    false
% 3.58/0.98  --res_prop_simpl_given                  true
% 3.58/0.98  --res_passive_queue_type                priority_queues
% 3.58/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.58/0.98  --res_passive_queues_freq               [15;5]
% 3.58/0.98  --res_forward_subs                      full
% 3.58/0.98  --res_backward_subs                     full
% 3.58/0.98  --res_forward_subs_resolution           true
% 3.58/0.98  --res_backward_subs_resolution          true
% 3.58/0.98  --res_orphan_elimination                true
% 3.58/0.98  --res_time_limit                        2.
% 3.58/0.98  --res_out_proof                         true
% 3.58/0.98  
% 3.58/0.98  ------ Superposition Options
% 3.58/0.98  
% 3.58/0.98  --superposition_flag                    true
% 3.58/0.98  --sup_passive_queue_type                priority_queues
% 3.58/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.58/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.58/0.98  --demod_completeness_check              fast
% 3.58/0.98  --demod_use_ground                      true
% 3.58/0.98  --sup_to_prop_solver                    passive
% 3.58/0.98  --sup_prop_simpl_new                    true
% 3.58/0.98  --sup_prop_simpl_given                  true
% 3.58/0.98  --sup_fun_splitting                     true
% 3.58/0.98  --sup_smt_interval                      50000
% 3.58/0.98  
% 3.58/0.98  ------ Superposition Simplification Setup
% 3.58/0.98  
% 3.58/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.58/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.58/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.58/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.58/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.58/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.58/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.58/0.98  --sup_immed_triv                        [TrivRules]
% 3.58/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/0.98  --sup_immed_bw_main                     []
% 3.58/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.58/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.58/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/0.98  --sup_input_bw                          []
% 3.58/0.98  
% 3.58/0.98  ------ Combination Options
% 3.58/0.98  
% 3.58/0.98  --comb_res_mult                         3
% 3.58/0.98  --comb_sup_mult                         2
% 3.58/0.98  --comb_inst_mult                        10
% 3.58/0.98  
% 3.58/0.98  ------ Debug Options
% 3.58/0.98  
% 3.58/0.98  --dbg_backtrace                         false
% 3.58/0.98  --dbg_dump_prop_clauses                 false
% 3.58/0.98  --dbg_dump_prop_clauses_file            -
% 3.58/0.98  --dbg_out_stat                          false
% 3.58/0.98  ------ Parsing...
% 3.58/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.58/0.98  
% 3.58/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.58/0.98  
% 3.58/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.58/0.98  
% 3.58/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/0.98  ------ Proving...
% 3.58/0.98  ------ Problem Properties 
% 3.58/0.98  
% 3.58/0.98  
% 3.58/0.98  clauses                                 21
% 3.58/0.98  conjectures                             6
% 3.58/0.98  EPR                                     1
% 3.58/0.98  Horn                                    16
% 3.58/0.98  unary                                   3
% 3.58/0.98  binary                                  6
% 3.58/0.98  lits                                    69
% 3.58/0.98  lits eq                                 4
% 3.58/0.98  fd_pure                                 0
% 3.58/0.98  fd_pseudo                               0
% 3.58/0.98  fd_cond                                 0
% 3.58/0.98  fd_pseudo_cond                          3
% 3.58/0.98  AC symbols                              0
% 3.58/0.98  
% 3.58/0.98  ------ Schedule dynamic 5 is on 
% 3.58/0.98  
% 3.58/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.58/0.98  
% 3.58/0.98  
% 3.58/0.98  ------ 
% 3.58/0.98  Current options:
% 3.58/0.98  ------ 
% 3.58/0.98  
% 3.58/0.98  ------ Input Options
% 3.58/0.98  
% 3.58/0.98  --out_options                           all
% 3.58/0.98  --tptp_safe_out                         true
% 3.58/0.98  --problem_path                          ""
% 3.58/0.98  --include_path                          ""
% 3.58/0.98  --clausifier                            res/vclausify_rel
% 3.58/0.98  --clausifier_options                    ""
% 3.58/0.98  --stdin                                 false
% 3.58/0.98  --stats_out                             all
% 3.58/0.98  
% 3.58/0.98  ------ General Options
% 3.58/0.98  
% 3.58/0.98  --fof                                   false
% 3.58/0.98  --time_out_real                         305.
% 3.58/0.98  --time_out_virtual                      -1.
% 3.58/0.98  --symbol_type_check                     false
% 3.58/0.98  --clausify_out                          false
% 3.58/0.98  --sig_cnt_out                           false
% 3.58/0.98  --trig_cnt_out                          false
% 3.58/0.98  --trig_cnt_out_tolerance                1.
% 3.58/0.98  --trig_cnt_out_sk_spl                   false
% 3.58/0.98  --abstr_cl_out                          false
% 3.58/0.98  
% 3.58/0.98  ------ Global Options
% 3.58/0.98  
% 3.58/0.98  --schedule                              default
% 3.58/0.98  --add_important_lit                     false
% 3.58/0.98  --prop_solver_per_cl                    1000
% 3.58/0.98  --min_unsat_core                        false
% 3.58/0.98  --soft_assumptions                      false
% 3.58/0.98  --soft_lemma_size                       3
% 3.58/0.98  --prop_impl_unit_size                   0
% 3.58/0.98  --prop_impl_unit                        []
% 3.58/0.98  --share_sel_clauses                     true
% 3.58/0.98  --reset_solvers                         false
% 3.58/0.98  --bc_imp_inh                            [conj_cone]
% 3.58/0.98  --conj_cone_tolerance                   3.
% 3.58/0.98  --extra_neg_conj                        none
% 3.58/0.98  --large_theory_mode                     true
% 3.58/0.98  --prolific_symb_bound                   200
% 3.58/0.98  --lt_threshold                          2000
% 3.58/0.98  --clause_weak_htbl                      true
% 3.58/0.98  --gc_record_bc_elim                     false
% 3.58/0.98  
% 3.58/0.98  ------ Preprocessing Options
% 3.58/0.98  
% 3.58/0.98  --preprocessing_flag                    true
% 3.58/0.98  --time_out_prep_mult                    0.1
% 3.58/0.98  --splitting_mode                        input
% 3.58/0.98  --splitting_grd                         true
% 3.58/0.98  --splitting_cvd                         false
% 3.58/0.98  --splitting_cvd_svl                     false
% 3.58/0.98  --splitting_nvd                         32
% 3.58/0.98  --sub_typing                            true
% 3.58/0.98  --prep_gs_sim                           true
% 3.58/0.98  --prep_unflatten                        true
% 3.58/0.98  --prep_res_sim                          true
% 3.58/0.98  --prep_upred                            true
% 3.58/0.98  --prep_sem_filter                       exhaustive
% 3.58/0.98  --prep_sem_filter_out                   false
% 3.58/0.98  --pred_elim                             true
% 3.58/0.98  --res_sim_input                         true
% 3.58/0.98  --eq_ax_congr_red                       true
% 3.58/0.98  --pure_diseq_elim                       true
% 3.58/0.98  --brand_transform                       false
% 3.58/0.98  --non_eq_to_eq                          false
% 3.58/0.98  --prep_def_merge                        true
% 3.58/0.98  --prep_def_merge_prop_impl              false
% 3.58/0.98  --prep_def_merge_mbd                    true
% 3.58/0.98  --prep_def_merge_tr_red                 false
% 3.58/0.98  --prep_def_merge_tr_cl                  false
% 3.58/0.98  --smt_preprocessing                     true
% 3.58/0.98  --smt_ac_axioms                         fast
% 3.58/0.98  --preprocessed_out                      false
% 3.58/0.98  --preprocessed_stats                    false
% 3.58/0.98  
% 3.58/0.98  ------ Abstraction refinement Options
% 3.58/0.98  
% 3.58/0.98  --abstr_ref                             []
% 3.58/0.98  --abstr_ref_prep                        false
% 3.58/0.98  --abstr_ref_until_sat                   false
% 3.58/0.98  --abstr_ref_sig_restrict                funpre
% 3.58/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.58/0.98  --abstr_ref_under                       []
% 3.58/0.98  
% 3.58/0.98  ------ SAT Options
% 3.58/0.98  
% 3.58/0.98  --sat_mode                              false
% 3.58/0.98  --sat_fm_restart_options                ""
% 3.58/0.98  --sat_gr_def                            false
% 3.58/0.98  --sat_epr_types                         true
% 3.58/0.98  --sat_non_cyclic_types                  false
% 3.58/0.98  --sat_finite_models                     false
% 3.58/0.98  --sat_fm_lemmas                         false
% 3.58/0.98  --sat_fm_prep                           false
% 3.58/0.98  --sat_fm_uc_incr                        true
% 3.58/0.98  --sat_out_model                         small
% 3.58/0.98  --sat_out_clauses                       false
% 3.58/0.98  
% 3.58/0.98  ------ QBF Options
% 3.58/0.98  
% 3.58/0.98  --qbf_mode                              false
% 3.58/0.98  --qbf_elim_univ                         false
% 3.58/0.98  --qbf_dom_inst                          none
% 3.58/0.98  --qbf_dom_pre_inst                      false
% 3.58/0.98  --qbf_sk_in                             false
% 3.58/0.98  --qbf_pred_elim                         true
% 3.58/0.98  --qbf_split                             512
% 3.58/0.98  
% 3.58/0.98  ------ BMC1 Options
% 3.58/0.98  
% 3.58/0.98  --bmc1_incremental                      false
% 3.58/0.98  --bmc1_axioms                           reachable_all
% 3.58/0.98  --bmc1_min_bound                        0
% 3.58/0.98  --bmc1_max_bound                        -1
% 3.58/0.98  --bmc1_max_bound_default                -1
% 3.58/0.98  --bmc1_symbol_reachability              true
% 3.58/0.98  --bmc1_property_lemmas                  false
% 3.58/0.98  --bmc1_k_induction                      false
% 3.58/0.98  --bmc1_non_equiv_states                 false
% 3.58/0.98  --bmc1_deadlock                         false
% 3.58/0.98  --bmc1_ucm                              false
% 3.58/0.98  --bmc1_add_unsat_core                   none
% 3.58/0.98  --bmc1_unsat_core_children              false
% 3.58/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.58/0.98  --bmc1_out_stat                         full
% 3.58/0.98  --bmc1_ground_init                      false
% 3.58/0.98  --bmc1_pre_inst_next_state              false
% 3.58/0.98  --bmc1_pre_inst_state                   false
% 3.58/0.98  --bmc1_pre_inst_reach_state             false
% 3.58/0.98  --bmc1_out_unsat_core                   false
% 3.58/0.98  --bmc1_aig_witness_out                  false
% 3.58/0.98  --bmc1_verbose                          false
% 3.58/0.98  --bmc1_dump_clauses_tptp                false
% 3.58/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.58/0.98  --bmc1_dump_file                        -
% 3.58/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.58/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.58/0.98  --bmc1_ucm_extend_mode                  1
% 3.58/0.98  --bmc1_ucm_init_mode                    2
% 3.58/0.98  --bmc1_ucm_cone_mode                    none
% 3.58/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.58/0.98  --bmc1_ucm_relax_model                  4
% 3.58/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.58/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.58/0.98  --bmc1_ucm_layered_model                none
% 3.58/0.98  --bmc1_ucm_max_lemma_size               10
% 3.58/0.98  
% 3.58/0.98  ------ AIG Options
% 3.58/0.98  
% 3.58/0.98  --aig_mode                              false
% 3.58/0.98  
% 3.58/0.98  ------ Instantiation Options
% 3.58/0.98  
% 3.58/0.98  --instantiation_flag                    true
% 3.58/0.98  --inst_sos_flag                         true
% 3.58/0.98  --inst_sos_phase                        true
% 3.58/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.58/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.58/0.98  --inst_lit_sel_side                     none
% 3.58/0.98  --inst_solver_per_active                1400
% 3.58/0.98  --inst_solver_calls_frac                1.
% 3.58/0.98  --inst_passive_queue_type               priority_queues
% 3.58/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.58/0.98  --inst_passive_queues_freq              [25;2]
% 3.58/0.98  --inst_dismatching                      true
% 3.58/0.98  --inst_eager_unprocessed_to_passive     true
% 3.58/0.98  --inst_prop_sim_given                   true
% 3.58/0.98  --inst_prop_sim_new                     false
% 3.58/0.98  --inst_subs_new                         false
% 3.58/0.98  --inst_eq_res_simp                      false
% 3.58/0.98  --inst_subs_given                       false
% 3.58/0.98  --inst_orphan_elimination               true
% 3.58/0.98  --inst_learning_loop_flag               true
% 3.58/0.98  --inst_learning_start                   3000
% 3.58/0.98  --inst_learning_factor                  2
% 3.58/0.98  --inst_start_prop_sim_after_learn       3
% 3.58/0.98  --inst_sel_renew                        solver
% 3.58/0.98  --inst_lit_activity_flag                true
% 3.58/0.98  --inst_restr_to_given                   false
% 3.58/0.98  --inst_activity_threshold               500
% 3.58/0.98  --inst_out_proof                        true
% 3.58/0.98  
% 3.58/0.98  ------ Resolution Options
% 3.58/0.98  
% 3.58/0.98  --resolution_flag                       false
% 3.58/0.98  --res_lit_sel                           adaptive
% 3.58/0.98  --res_lit_sel_side                      none
% 3.58/0.98  --res_ordering                          kbo
% 3.58/0.98  --res_to_prop_solver                    active
% 3.58/0.98  --res_prop_simpl_new                    false
% 3.58/0.98  --res_prop_simpl_given                  true
% 3.58/0.98  --res_passive_queue_type                priority_queues
% 3.58/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.58/0.98  --res_passive_queues_freq               [15;5]
% 3.58/0.98  --res_forward_subs                      full
% 3.58/0.98  --res_backward_subs                     full
% 3.58/0.98  --res_forward_subs_resolution           true
% 3.58/0.98  --res_backward_subs_resolution          true
% 3.58/0.98  --res_orphan_elimination                true
% 3.58/0.98  --res_time_limit                        2.
% 3.58/0.98  --res_out_proof                         true
% 3.58/0.98  
% 3.58/0.98  ------ Superposition Options
% 3.58/0.98  
% 3.58/0.98  --superposition_flag                    true
% 3.58/0.98  --sup_passive_queue_type                priority_queues
% 3.58/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.58/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.58/0.98  --demod_completeness_check              fast
% 3.58/0.98  --demod_use_ground                      true
% 3.58/0.98  --sup_to_prop_solver                    passive
% 3.58/0.98  --sup_prop_simpl_new                    true
% 3.58/0.98  --sup_prop_simpl_given                  true
% 3.58/0.98  --sup_fun_splitting                     true
% 3.58/0.98  --sup_smt_interval                      50000
% 3.58/0.98  
% 3.58/0.98  ------ Superposition Simplification Setup
% 3.58/0.98  
% 3.58/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.58/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.58/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.58/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.58/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.58/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.58/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.58/0.98  --sup_immed_triv                        [TrivRules]
% 3.58/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/0.98  --sup_immed_bw_main                     []
% 3.58/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.58/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.58/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/0.98  --sup_input_bw                          []
% 3.58/0.98  
% 3.58/0.98  ------ Combination Options
% 3.58/0.98  
% 3.58/0.98  --comb_res_mult                         3
% 3.58/0.98  --comb_sup_mult                         2
% 3.58/0.98  --comb_inst_mult                        10
% 3.58/0.98  
% 3.58/0.98  ------ Debug Options
% 3.58/0.98  
% 3.58/0.98  --dbg_backtrace                         false
% 3.58/0.98  --dbg_dump_prop_clauses                 false
% 3.58/0.98  --dbg_dump_prop_clauses_file            -
% 3.58/0.98  --dbg_out_stat                          false
% 3.58/0.98  
% 3.58/0.98  
% 3.58/0.98  
% 3.58/0.98  
% 3.58/0.98  ------ Proving...
% 3.58/0.98  
% 3.58/0.98  
% 3.58/0.98  % SZS status Theorem for theBenchmark.p
% 3.58/0.98  
% 3.58/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.58/0.98  
% 3.58/0.98  fof(f6,axiom,(
% 3.58/0.98    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.98  
% 3.58/0.98  fof(f16,plain,(
% 3.58/0.98    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.58/0.98    inference(ennf_transformation,[],[f6])).
% 3.58/0.98  
% 3.58/0.98  fof(f17,plain,(
% 3.58/0.98    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.58/0.98    inference(flattening,[],[f16])).
% 3.58/0.98  
% 3.58/0.98  fof(f48,plain,(
% 3.58/0.98    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.58/0.98    inference(cnf_transformation,[],[f17])).
% 3.58/0.98  
% 3.58/0.98  fof(f9,conjecture,(
% 3.58/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ! [X5,X6] : (r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) <=> ? [X7] : (r2_hidden(k4_tarski(X7,X6),X4) & r2_hidden(k4_tarski(X5,X7),X3) & m1_subset_1(X7,X1))))))))),
% 3.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.98  
% 3.58/0.98  fof(f10,negated_conjecture,(
% 3.58/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ! [X5,X6] : (r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) <=> ? [X7] : (r2_hidden(k4_tarski(X7,X6),X4) & r2_hidden(k4_tarski(X5,X7),X3) & m1_subset_1(X7,X1))))))))),
% 3.58/0.98    inference(negated_conjecture,[],[f9])).
% 3.58/0.98  
% 3.58/0.98  fof(f11,plain,(
% 3.58/0.98    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ! [X5,X6] : (r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) <=> ? [X7] : (r2_hidden(k4_tarski(X7,X6),X4) & r2_hidden(k4_tarski(X5,X7),X3) & m1_subset_1(X7,X1)))))),
% 3.58/0.98    inference(pure_predicate_removal,[],[f10])).
% 3.58/0.98  
% 3.58/0.98  fof(f20,plain,(
% 3.58/0.98    ? [X0,X1,X2,X3] : (? [X4] : (? [X5,X6] : (r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) <~> ? [X7] : (r2_hidden(k4_tarski(X7,X6),X4) & r2_hidden(k4_tarski(X5,X7),X3) & m1_subset_1(X7,X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.58/0.98    inference(ennf_transformation,[],[f11])).
% 3.58/0.98  
% 3.58/0.98  fof(f29,plain,(
% 3.58/0.98    ? [X0,X1,X2,X3] : (? [X4] : (? [X5,X6] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),X4) | ~r2_hidden(k4_tarski(X5,X7),X3) | ~m1_subset_1(X7,X1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))) & (? [X7] : (r2_hidden(k4_tarski(X7,X6),X4) & r2_hidden(k4_tarski(X5,X7),X3) & m1_subset_1(X7,X1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.58/0.98    inference(nnf_transformation,[],[f20])).
% 3.58/0.98  
% 3.58/0.98  fof(f30,plain,(
% 3.58/0.98    ? [X0,X1,X2,X3] : (? [X4] : (? [X5,X6] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),X4) | ~r2_hidden(k4_tarski(X5,X7),X3) | ~m1_subset_1(X7,X1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))) & (? [X8] : (r2_hidden(k4_tarski(X8,X6),X4) & r2_hidden(k4_tarski(X5,X8),X3) & m1_subset_1(X8,X1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.58/0.98    inference(rectify,[],[f29])).
% 3.58/0.98  
% 3.58/0.98  fof(f34,plain,(
% 3.58/0.98    ( ! [X6,X4,X5,X3,X1] : (? [X8] : (r2_hidden(k4_tarski(X8,X6),X4) & r2_hidden(k4_tarski(X5,X8),X3) & m1_subset_1(X8,X1)) => (r2_hidden(k4_tarski(sK11,X6),X4) & r2_hidden(k4_tarski(X5,sK11),X3) & m1_subset_1(sK11,X1))) )),
% 3.58/0.98    introduced(choice_axiom,[])).
% 3.58/0.98  
% 3.58/0.98  fof(f33,plain,(
% 3.58/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5,X6] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),X4) | ~r2_hidden(k4_tarski(X5,X7),X3) | ~m1_subset_1(X7,X1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))) & (? [X8] : (r2_hidden(k4_tarski(X8,X6),X4) & r2_hidden(k4_tarski(X5,X8),X3) & m1_subset_1(X8,X1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)))) => ((! [X7] : (~r2_hidden(k4_tarski(X7,sK10),X4) | ~r2_hidden(k4_tarski(sK9,X7),X3) | ~m1_subset_1(X7,X1)) | ~r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(X0,X1,X1,X2,X3,X4))) & (? [X8] : (r2_hidden(k4_tarski(X8,sK10),X4) & r2_hidden(k4_tarski(sK9,X8),X3) & m1_subset_1(X8,X1)) | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(X0,X1,X1,X2,X3,X4))))) )),
% 3.58/0.98    introduced(choice_axiom,[])).
% 3.58/0.98  
% 3.58/0.98  fof(f32,plain,(
% 3.58/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5,X6] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),X4) | ~r2_hidden(k4_tarski(X5,X7),X3) | ~m1_subset_1(X7,X1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))) & (? [X8] : (r2_hidden(k4_tarski(X8,X6),X4) & r2_hidden(k4_tarski(X5,X8),X3) & m1_subset_1(X8,X1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) => (? [X6,X5] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),sK8) | ~r2_hidden(k4_tarski(X5,X7),X3) | ~m1_subset_1(X7,X1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,sK8))) & (? [X8] : (r2_hidden(k4_tarski(X8,X6),sK8) & r2_hidden(k4_tarski(X5,X8),X3) & m1_subset_1(X8,X1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,sK8)))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))) )),
% 3.58/0.98    introduced(choice_axiom,[])).
% 3.58/0.98  
% 3.58/0.98  fof(f31,plain,(
% 3.58/0.98    ? [X0,X1,X2,X3] : (? [X4] : (? [X5,X6] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),X4) | ~r2_hidden(k4_tarski(X5,X7),X3) | ~m1_subset_1(X7,X1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))) & (? [X8] : (r2_hidden(k4_tarski(X8,X6),X4) & r2_hidden(k4_tarski(X5,X8),X3) & m1_subset_1(X8,X1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (? [X4] : (? [X6,X5] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),X4) | ~r2_hidden(k4_tarski(X5,X7),sK7) | ~m1_subset_1(X7,sK5)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK4,sK5,sK5,sK6,sK7,X4))) & (? [X8] : (r2_hidden(k4_tarski(X8,X6),X4) & r2_hidden(k4_tarski(X5,X8),sK7) & m1_subset_1(X8,sK5)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK4,sK5,sK5,sK6,sK7,X4)))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))))),
% 3.58/0.98    introduced(choice_axiom,[])).
% 3.58/0.98  
% 3.58/0.98  fof(f35,plain,(
% 3.58/0.98    (((! [X7] : (~r2_hidden(k4_tarski(X7,sK10),sK8) | ~r2_hidden(k4_tarski(sK9,X7),sK7) | ~m1_subset_1(X7,sK5)) | ~r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8))) & ((r2_hidden(k4_tarski(sK11,sK10),sK8) & r2_hidden(k4_tarski(sK9,sK11),sK7) & m1_subset_1(sK11,sK5)) | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.58/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10,sK11])],[f30,f34,f33,f32,f31])).
% 3.58/0.98  
% 3.58/0.98  fof(f51,plain,(
% 3.58/0.98    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.58/0.98    inference(cnf_transformation,[],[f35])).
% 3.58/0.98  
% 3.58/0.98  fof(f52,plain,(
% 3.58/0.98    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.58/0.98    inference(cnf_transformation,[],[f35])).
% 3.58/0.98  
% 3.58/0.98  fof(f8,axiom,(
% 3.58/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 3.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.98  
% 3.58/0.98  fof(f18,plain,(
% 3.58/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.58/0.98    inference(ennf_transformation,[],[f8])).
% 3.58/0.98  
% 3.58/0.98  fof(f19,plain,(
% 3.58/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.58/0.98    inference(flattening,[],[f18])).
% 3.58/0.98  
% 3.58/0.98  fof(f50,plain,(
% 3.58/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.58/0.98    inference(cnf_transformation,[],[f19])).
% 3.58/0.98  
% 3.58/0.98  fof(f54,plain,(
% 3.58/0.98    r2_hidden(k4_tarski(sK9,sK11),sK7) | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8))),
% 3.58/0.98    inference(cnf_transformation,[],[f35])).
% 3.58/0.98  
% 3.58/0.98  fof(f5,axiom,(
% 3.58/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 3.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.98  
% 3.58/0.98  fof(f15,plain,(
% 3.58/0.98    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.58/0.98    inference(ennf_transformation,[],[f5])).
% 3.58/0.98  
% 3.58/0.98  fof(f23,plain,(
% 3.58/0.98    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.58/0.98    inference(nnf_transformation,[],[f15])).
% 3.58/0.98  
% 3.58/0.98  fof(f24,plain,(
% 3.58/0.98    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.58/0.98    inference(rectify,[],[f23])).
% 3.58/0.98  
% 3.58/0.98  fof(f27,plain,(
% 3.58/0.98    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)))),
% 3.58/0.98    introduced(choice_axiom,[])).
% 3.58/0.98  
% 3.58/0.98  fof(f26,plain,(
% 3.58/0.98    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0)))) )),
% 3.58/0.98    introduced(choice_axiom,[])).
% 3.58/0.98  
% 3.58/0.98  fof(f25,plain,(
% 3.58/0.98    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK1(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2))))),
% 3.58/0.98    introduced(choice_axiom,[])).
% 3.58/0.98  
% 3.58/0.98  fof(f28,plain,(
% 3.58/0.98    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.58/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f27,f26,f25])).
% 3.58/0.98  
% 3.58/0.98  fof(f43,plain,(
% 3.58/0.98    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.58/0.98    inference(cnf_transformation,[],[f28])).
% 3.58/0.98  
% 3.58/0.98  fof(f58,plain,(
% 3.58/0.98    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.58/0.98    inference(equality_resolution,[],[f43])).
% 3.58/0.98  
% 3.58/0.98  fof(f2,axiom,(
% 3.58/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.98  
% 3.58/0.98  fof(f12,plain,(
% 3.58/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.58/0.98    inference(ennf_transformation,[],[f2])).
% 3.58/0.98  
% 3.58/0.98  fof(f39,plain,(
% 3.58/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.58/0.98    inference(cnf_transformation,[],[f12])).
% 3.58/0.98  
% 3.58/0.98  fof(f1,axiom,(
% 3.58/0.98    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.98  
% 3.58/0.98  fof(f21,plain,(
% 3.58/0.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.58/0.98    inference(nnf_transformation,[],[f1])).
% 3.58/0.98  
% 3.58/0.98  fof(f22,plain,(
% 3.58/0.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.58/0.98    inference(flattening,[],[f21])).
% 3.58/0.98  
% 3.58/0.98  fof(f36,plain,(
% 3.58/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.58/0.98    inference(cnf_transformation,[],[f22])).
% 3.58/0.98  
% 3.58/0.98  fof(f7,axiom,(
% 3.58/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.98  
% 3.58/0.98  fof(f49,plain,(
% 3.58/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.58/0.98    inference(cnf_transformation,[],[f7])).
% 3.58/0.98  
% 3.58/0.98  fof(f4,axiom,(
% 3.58/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.98  
% 3.58/0.98  fof(f14,plain,(
% 3.58/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.58/0.98    inference(ennf_transformation,[],[f4])).
% 3.58/0.98  
% 3.58/0.98  fof(f41,plain,(
% 3.58/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.58/0.98    inference(cnf_transformation,[],[f14])).
% 3.58/0.98  
% 3.58/0.98  fof(f3,axiom,(
% 3.58/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.98  
% 3.58/0.98  fof(f13,plain,(
% 3.58/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.58/0.98    inference(ennf_transformation,[],[f3])).
% 3.58/0.98  
% 3.58/0.98  fof(f40,plain,(
% 3.58/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.58/0.98    inference(cnf_transformation,[],[f13])).
% 3.58/0.98  
% 3.58/0.98  fof(f44,plain,(
% 3.58/0.98    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.58/0.98    inference(cnf_transformation,[],[f28])).
% 3.58/0.98  
% 3.58/0.98  fof(f57,plain,(
% 3.58/0.98    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.58/0.98    inference(equality_resolution,[],[f44])).
% 3.58/0.98  
% 3.58/0.98  fof(f42,plain,(
% 3.58/0.98    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.58/0.98    inference(cnf_transformation,[],[f28])).
% 3.58/0.98  
% 3.58/0.98  fof(f59,plain,(
% 3.58/0.98    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.58/0.98    inference(equality_resolution,[],[f42])).
% 3.58/0.98  
% 3.58/0.98  fof(f56,plain,(
% 3.58/0.98    ( ! [X7] : (~r2_hidden(k4_tarski(X7,sK10),sK8) | ~r2_hidden(k4_tarski(sK9,X7),sK7) | ~m1_subset_1(X7,sK5) | ~r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8))) )),
% 3.58/0.98    inference(cnf_transformation,[],[f35])).
% 3.58/0.98  
% 3.58/0.98  fof(f53,plain,(
% 3.58/0.98    m1_subset_1(sK11,sK5) | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8))),
% 3.58/0.98    inference(cnf_transformation,[],[f35])).
% 3.58/0.98  
% 3.58/0.98  fof(f55,plain,(
% 3.58/0.98    r2_hidden(k4_tarski(sK11,sK10),sK8) | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8))),
% 3.58/0.98    inference(cnf_transformation,[],[f35])).
% 3.58/0.98  
% 3.58/0.98  cnf(c_12,plain,
% 3.58/0.98      ( ~ v1_relat_1(X0)
% 3.58/0.98      | ~ v1_relat_1(X1)
% 3.58/0.98      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 3.58/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_585,plain,
% 3.58/0.98      ( v1_relat_1(X0) != iProver_top
% 3.58/0.98      | v1_relat_1(X1) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 3.58/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_20,negated_conjecture,
% 3.58/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.58/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_577,plain,
% 3.58/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.58/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_19,negated_conjecture,
% 3.58/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.58/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_578,plain,
% 3.58/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.58/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_14,plain,
% 3.58/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.58/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.58/0.98      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.58/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_583,plain,
% 3.58/0.98      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.58/0.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.58/0.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.58/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_1203,plain,
% 3.58/0.98      ( k4_relset_1(X0,X1,sK5,sK6,X2,sK8) = k5_relat_1(X2,sK8)
% 3.58/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_578,c_583]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_1469,plain,
% 3.58/0.98      ( k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8) = k5_relat_1(sK7,sK8) ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_577,c_1203]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_17,negated_conjecture,
% 3.58/0.98      ( r2_hidden(k4_tarski(sK9,sK11),sK7)
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) ),
% 3.58/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_580,plain,
% 3.58/0.98      ( r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) = iProver_top ),
% 3.58/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_1488,plain,
% 3.58/0.98      ( r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK10),k5_relat_1(sK7,sK8)) = iProver_top ),
% 3.58/0.98      inference(demodulation,[status(thm)],[c_1469,c_580]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_10,plain,
% 3.58/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 3.58/0.98      | r2_hidden(k4_tarski(sK3(X2,X3,X0,X1),X1),X3)
% 3.58/0.98      | ~ v1_relat_1(X2)
% 3.58/0.98      | ~ v1_relat_1(X3)
% 3.58/0.98      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 3.58/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_587,plain,
% 3.58/0.98      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK3(X2,X3,X0,X1),X1),X3) = iProver_top
% 3.58/0.98      | v1_relat_1(X2) != iProver_top
% 3.58/0.98      | v1_relat_1(X3) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
% 3.58/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_3,plain,
% 3.58/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.58/0.98      | ~ r2_hidden(X2,X0)
% 3.58/0.98      | r2_hidden(X2,X1) ),
% 3.58/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_594,plain,
% 3.58/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.58/0.98      | r2_hidden(X2,X0) != iProver_top
% 3.58/0.98      | r2_hidden(X2,X1) = iProver_top ),
% 3.58/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_1746,plain,
% 3.58/0.98      ( r2_hidden(X0,k2_zfmisc_1(sK5,sK6)) = iProver_top
% 3.58/0.98      | r2_hidden(X0,sK8) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_578,c_594]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_2,plain,
% 3.58/0.98      ( r2_hidden(X0,X1)
% 3.58/0.98      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.58/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_595,plain,
% 3.58/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 3.58/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_1895,plain,
% 3.58/0.98      ( r2_hidden(X0,sK5) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_1746,c_595]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_2773,plain,
% 3.58/0.98      ( r2_hidden(sK3(X0,sK8,X1,X2),sK5) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(X0) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_587,c_1895]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_13,plain,
% 3.58/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.58/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_584,plain,
% 3.58/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.58/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5,plain,
% 3.58/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.58/0.98      | ~ v1_relat_1(X1)
% 3.58/0.98      | v1_relat_1(X0) ),
% 3.58/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_592,plain,
% 3.58/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.58/0.98      | v1_relat_1(X1) != iProver_top
% 3.58/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.58/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_1714,plain,
% 3.58/0.98      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
% 3.58/0.98      | v1_relat_1(sK8) = iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_578,c_592]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_1821,plain,
% 3.58/0.98      ( v1_relat_1(sK8) = iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_584,c_1714]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5166,plain,
% 3.58/0.98      ( v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(X0) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | r2_hidden(sK3(X0,sK8,X1,X2),sK5) = iProver_top ),
% 3.58/0.98      inference(global_propositional_subsumption,
% 3.58/0.98                [status(thm)],
% 3.58/0.98                [c_2773,c_1821]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5167,plain,
% 3.58/0.98      ( r2_hidden(sK3(X0,sK8,X1,X2),sK5) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(X0) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top ),
% 3.58/0.98      inference(renaming,[status(thm)],[c_5166]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5178,plain,
% 3.58/0.98      ( r2_hidden(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(sK7) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_1488,c_5167]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_1715,plain,
% 3.58/0.98      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
% 3.58/0.98      | v1_relat_1(sK7) = iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_577,c_592]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_1824,plain,
% 3.58/0.98      ( v1_relat_1(sK7) = iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_584,c_1715]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5268,plain,
% 3.58/0.98      ( v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
% 3.58/0.98      | r2_hidden(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top ),
% 3.58/0.98      inference(global_propositional_subsumption,
% 3.58/0.98                [status(thm)],
% 3.58/0.98                [c_5178,c_1824]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5269,plain,
% 3.58/0.98      ( r2_hidden(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
% 3.58/0.98      inference(renaming,[status(thm)],[c_5268]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_4,plain,
% 3.58/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.58/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_593,plain,
% 3.58/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 3.58/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.58/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5272,plain,
% 3.58/0.98      ( m1_subset_1(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_5269,c_593]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_9,plain,
% 3.58/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.58/0.98      | ~ r2_hidden(k4_tarski(X3,X0),X4)
% 3.58/0.98      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
% 3.58/0.98      | ~ v1_relat_1(X4)
% 3.58/0.98      | ~ v1_relat_1(X2)
% 3.58/0.98      | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
% 3.58/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_588,plain,
% 3.58/0.98      ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X3,X0),X4) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2)) = iProver_top
% 3.58/0.98      | v1_relat_1(X2) != iProver_top
% 3.58/0.98      | v1_relat_1(X4) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(X4,X2)) != iProver_top ),
% 3.58/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_2545,plain,
% 3.58/0.98      ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X0,X3),k5_relat_1(X2,k2_zfmisc_1(sK5,sK6))) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X1,X3),sK8) != iProver_top
% 3.58/0.98      | v1_relat_1(X2) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(X2,k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.58/0.98      | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_1746,c_588]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_2911,plain,
% 3.58/0.98      ( r2_hidden(k4_tarski(sK9,X0),k5_relat_1(k5_relat_1(sK7,sK8),k2_zfmisc_1(sK5,sK6))) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK10,X0),sK8) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(k5_relat_1(sK7,sK8),k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_1488,c_2545]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_11,plain,
% 3.58/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 3.58/0.98      | r2_hidden(k4_tarski(X0,sK3(X2,X3,X0,X1)),X2)
% 3.58/0.98      | ~ v1_relat_1(X2)
% 3.58/0.98      | ~ v1_relat_1(X3)
% 3.58/0.98      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 3.58/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_586,plain,
% 3.58/0.98      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X0,sK3(X2,X3,X0,X1)),X2) = iProver_top
% 3.58/0.98      | v1_relat_1(X2) != iProver_top
% 3.58/0.98      | v1_relat_1(X3) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
% 3.58/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_15,negated_conjecture,
% 3.58/0.98      ( ~ m1_subset_1(X0,sK5)
% 3.58/0.98      | ~ r2_hidden(k4_tarski(X0,sK10),sK8)
% 3.58/0.98      | ~ r2_hidden(k4_tarski(sK9,X0),sK7)
% 3.58/0.98      | ~ r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) ),
% 3.58/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_582,plain,
% 3.58/0.98      ( m1_subset_1(X0,sK5) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X0,sK10),sK8) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,X0),sK7) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) != iProver_top ),
% 3.58/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_1004,plain,
% 3.58/0.98      ( m1_subset_1(X0,sK5) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X0,sK10),sK8) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,X0),sK7) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_580,c_582]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_1947,plain,
% 3.58/0.98      ( m1_subset_1(sK3(X0,sK8,X1,sK10),sK5) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X1,sK10),k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK3(X0,sK8,X1,sK10)),sK7) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
% 3.58/0.98      | v1_relat_1(X0) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_587,c_1004]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_3323,plain,
% 3.58/0.98      ( v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(X0) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK3(X0,sK8,X1,sK10)),sK7) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X1,sK10),k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | m1_subset_1(sK3(X0,sK8,X1,sK10),sK5) != iProver_top ),
% 3.58/0.98      inference(global_propositional_subsumption,
% 3.58/0.98                [status(thm)],
% 3.58/0.98                [c_1947,c_1821]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_3324,plain,
% 3.58/0.98      ( m1_subset_1(sK3(X0,sK8,X1,sK10),sK5) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X1,sK10),k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK3(X0,sK8,X1,sK10)),sK7) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
% 3.58/0.98      | v1_relat_1(X0) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top ),
% 3.58/0.98      inference(renaming,[status(thm)],[c_3323]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_3329,plain,
% 3.58/0.98      ( m1_subset_1(sK3(sK7,sK8,sK9,sK10),sK5) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK10),k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(sK7) != iProver_top
% 3.58/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_586,c_3324]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5282,plain,
% 3.58/0.98      ( v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top ),
% 3.58/0.98      inference(global_propositional_subsumption,
% 3.58/0.98                [status(thm)],
% 3.58/0.98                [c_2911,c_1488,c_1821,c_1824,c_3329,c_5272]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5283,plain,
% 3.58/0.98      ( r2_hidden(k4_tarski(sK9,sK11),sK7) = iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
% 3.58/0.98      inference(renaming,[status(thm)],[c_5282]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_18,negated_conjecture,
% 3.58/0.98      ( m1_subset_1(sK11,sK5)
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) ),
% 3.58/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_579,plain,
% 3.58/0.98      ( m1_subset_1(sK11,sK5) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) = iProver_top ),
% 3.58/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_1489,plain,
% 3.58/0.98      ( m1_subset_1(sK11,sK5) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK10),k5_relat_1(sK7,sK8)) = iProver_top ),
% 3.58/0.98      inference(demodulation,[status(thm)],[c_1469,c_579]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5180,plain,
% 3.58/0.98      ( m1_subset_1(sK11,sK5) = iProver_top
% 3.58/0.98      | r2_hidden(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(sK7) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_1489,c_5167]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5261,plain,
% 3.58/0.98      ( v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | r2_hidden(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
% 3.58/0.98      | m1_subset_1(sK11,sK5) = iProver_top ),
% 3.58/0.98      inference(global_propositional_subsumption,
% 3.58/0.98                [status(thm)],
% 3.58/0.98                [c_5180,c_1824]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5262,plain,
% 3.58/0.98      ( m1_subset_1(sK11,sK5) = iProver_top
% 3.58/0.98      | r2_hidden(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
% 3.58/0.98      inference(renaming,[status(thm)],[c_5261]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5265,plain,
% 3.58/0.98      ( m1_subset_1(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
% 3.58/0.98      | m1_subset_1(sK11,sK5) = iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_5262,c_593]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_864,plain,
% 3.58/0.98      ( m1_subset_1(X0,sK5) != iProver_top
% 3.58/0.98      | m1_subset_1(sK11,sK5) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X0,sK10),sK8) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,X0),sK7) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_579,c_582]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_1948,plain,
% 3.58/0.98      ( m1_subset_1(sK3(X0,sK8,X1,sK10),sK5) != iProver_top
% 3.58/0.98      | m1_subset_1(sK11,sK5) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X1,sK10),k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK3(X0,sK8,X1,sK10)),sK7) != iProver_top
% 3.58/0.98      | v1_relat_1(X0) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_587,c_864]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_3128,plain,
% 3.58/0.98      ( v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(X0) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK3(X0,sK8,X1,sK10)),sK7) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X1,sK10),k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | m1_subset_1(sK11,sK5) = iProver_top
% 3.58/0.98      | m1_subset_1(sK3(X0,sK8,X1,sK10),sK5) != iProver_top ),
% 3.58/0.98      inference(global_propositional_subsumption,
% 3.58/0.98                [status(thm)],
% 3.58/0.98                [c_1948,c_1821]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_3129,plain,
% 3.58/0.98      ( m1_subset_1(sK3(X0,sK8,X1,sK10),sK5) != iProver_top
% 3.58/0.98      | m1_subset_1(sK11,sK5) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X1,sK10),k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK3(X0,sK8,X1,sK10)),sK7) != iProver_top
% 3.58/0.98      | v1_relat_1(X0) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top ),
% 3.58/0.98      inference(renaming,[status(thm)],[c_3128]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_3134,plain,
% 3.58/0.98      ( m1_subset_1(sK3(sK7,sK8,sK9,sK10),sK5) != iProver_top
% 3.58/0.98      | m1_subset_1(sK11,sK5) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK10),k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(sK7) != iProver_top
% 3.58/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_586,c_3129]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5403,plain,
% 3.58/0.98      ( m1_subset_1(sK11,sK5) = iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
% 3.58/0.98      inference(global_propositional_subsumption,
% 3.58/0.98                [status(thm)],
% 3.58/0.98                [c_5265,c_1489,c_1821,c_1824,c_3134]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5407,plain,
% 3.58/0.98      ( m1_subset_1(sK11,sK5) = iProver_top
% 3.58/0.98      | v1_relat_1(sK7) != iProver_top
% 3.58/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_585,c_5403]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_16,negated_conjecture,
% 3.58/0.98      ( r2_hidden(k4_tarski(sK11,sK10),sK8)
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) ),
% 3.58/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_581,plain,
% 3.58/0.98      ( r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK10),k4_relset_1(sK4,sK5,sK5,sK6,sK7,sK8)) = iProver_top ),
% 3.58/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_1487,plain,
% 3.58/0.98      ( r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK10),k5_relat_1(sK7,sK8)) = iProver_top ),
% 3.58/0.98      inference(demodulation,[status(thm)],[c_1469,c_581]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_2912,plain,
% 3.58/0.98      ( r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,X0),k5_relat_1(k5_relat_1(sK7,sK8),k2_zfmisc_1(sK5,sK6))) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK10,X0),sK8) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(k5_relat_1(sK7,sK8),k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_1487,c_2545]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_1009,plain,
% 3.58/0.98      ( m1_subset_1(X0,sK5) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X0,sK10),sK8) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,X0),sK7) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_581,c_582]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_1946,plain,
% 3.58/0.98      ( m1_subset_1(sK3(X0,sK8,X1,sK10),sK5) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X1,sK10),k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK3(X0,sK8,X1,sK10)),sK7) != iProver_top
% 3.58/0.98      | v1_relat_1(X0) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_587,c_1009]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_3174,plain,
% 3.58/0.98      ( v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(X0) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK3(X0,sK8,X1,sK10)),sK7) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X1,sK10),k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | m1_subset_1(sK3(X0,sK8,X1,sK10),sK5) != iProver_top ),
% 3.58/0.98      inference(global_propositional_subsumption,
% 3.58/0.98                [status(thm)],
% 3.58/0.98                [c_1946,c_1821]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_3175,plain,
% 3.58/0.98      ( m1_subset_1(sK3(X0,sK8,X1,sK10),sK5) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X1,sK10),k5_relat_1(X0,sK8)) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK3(X0,sK8,X1,sK10)),sK7) != iProver_top
% 3.58/0.98      | v1_relat_1(X0) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(X0,sK8)) != iProver_top ),
% 3.58/0.98      inference(renaming,[status(thm)],[c_3174]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_3180,plain,
% 3.58/0.98      ( m1_subset_1(sK3(sK7,sK8,sK9,sK10),sK5) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK10),k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(sK7) != iProver_top
% 3.58/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_586,c_3175]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5179,plain,
% 3.58/0.98      ( r2_hidden(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(sK7) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_1487,c_5167]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5275,plain,
% 3.58/0.98      ( v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
% 3.58/0.98      | r2_hidden(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top ),
% 3.58/0.98      inference(global_propositional_subsumption,
% 3.58/0.98                [status(thm)],
% 3.58/0.98                [c_5179,c_1824]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5276,plain,
% 3.58/0.98      ( r2_hidden(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
% 3.58/0.98      inference(renaming,[status(thm)],[c_5275]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5279,plain,
% 3.58/0.98      ( m1_subset_1(sK3(sK7,sK8,sK9,sK10),sK5) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_5276,c_593]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5308,plain,
% 3.58/0.98      ( v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top ),
% 3.58/0.98      inference(global_propositional_subsumption,
% 3.58/0.98                [status(thm)],
% 3.58/0.98                [c_2912,c_1487,c_1821,c_1824,c_3180,c_5279]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5309,plain,
% 3.58/0.98      ( r2_hidden(k4_tarski(sK11,sK10),sK8) = iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
% 3.58/0.98      inference(renaming,[status(thm)],[c_5308]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5315,plain,
% 3.58/0.98      ( r2_hidden(k4_tarski(X0,sK11),X1) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X0,sK10),k5_relat_1(X1,sK8)) = iProver_top
% 3.58/0.98      | v1_relat_1(X1) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(X1,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_5309,c_588]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5565,plain,
% 3.58/0.98      ( v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(X1,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(X1) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X0,sK10),k5_relat_1(X1,sK8)) = iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X0,sK11),X1) != iProver_top ),
% 3.58/0.98      inference(global_propositional_subsumption,
% 3.58/0.98                [status(thm)],
% 3.58/0.98                [c_5315,c_1821]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5566,plain,
% 3.58/0.98      ( r2_hidden(k4_tarski(X0,sK11),X1) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X0,sK10),k5_relat_1(X1,sK8)) = iProver_top
% 3.58/0.98      | v1_relat_1(X1) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(X1,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
% 3.58/0.98      inference(renaming,[status(thm)],[c_5565]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_1490,plain,
% 3.58/0.98      ( m1_subset_1(X0,sK5) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X0,sK10),sK8) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,X0),sK7) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK10),k5_relat_1(sK7,sK8)) != iProver_top ),
% 3.58/0.98      inference(demodulation,[status(thm)],[c_1469,c_582]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5575,plain,
% 3.58/0.98      ( m1_subset_1(X0,sK5) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X0,sK10),sK8) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,X0),sK7) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK11),sK7) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | v1_relat_1(sK7) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_5566,c_1490]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5620,plain,
% 3.58/0.98      ( v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top
% 3.58/0.98      | m1_subset_1(X0,sK5) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X0,sK10),sK8) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,X0),sK7) != iProver_top ),
% 3.58/0.98      inference(global_propositional_subsumption,
% 3.58/0.98                [status(thm)],
% 3.58/0.98                [c_5575,c_1488,c_1821,c_1824,c_3329,c_5272]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5621,plain,
% 3.58/0.98      ( m1_subset_1(X0,sK5) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(X0,sK10),sK8) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,X0),sK7) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
% 3.58/0.98      inference(renaming,[status(thm)],[c_5620]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5627,plain,
% 3.58/0.98      ( m1_subset_1(sK11,sK5) != iProver_top
% 3.58/0.98      | r2_hidden(k4_tarski(sK9,sK11),sK7) != iProver_top
% 3.58/0.98      | v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_5309,c_5621]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5678,plain,
% 3.58/0.98      ( v1_relat_1(k5_relat_1(sK7,sK8)) != iProver_top ),
% 3.58/0.98      inference(global_propositional_subsumption,
% 3.58/0.98                [status(thm)],
% 3.58/0.98                [c_5272,c_1821,c_1824,c_5283,c_5407,c_5627]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(c_5682,plain,
% 3.58/0.98      ( v1_relat_1(sK7) != iProver_top | v1_relat_1(sK8) != iProver_top ),
% 3.58/0.98      inference(superposition,[status(thm)],[c_585,c_5678]) ).
% 3.58/0.98  
% 3.58/0.98  cnf(contradiction,plain,
% 3.58/0.98      ( $false ),
% 3.58/0.98      inference(minisat,[status(thm)],[c_5682,c_1824,c_1821]) ).
% 3.58/0.98  
% 3.58/0.98  
% 3.58/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.58/0.98  
% 3.58/0.98  ------                               Statistics
% 3.58/0.98  
% 3.58/0.98  ------ General
% 3.58/0.98  
% 3.58/0.98  abstr_ref_over_cycles:                  0
% 3.58/0.98  abstr_ref_under_cycles:                 0
% 3.58/0.98  gc_basic_clause_elim:                   0
% 3.58/0.98  forced_gc_time:                         0
% 3.58/0.98  parsing_time:                           0.008
% 3.58/0.98  unif_index_cands_time:                  0.
% 3.58/0.98  unif_index_add_time:                    0.
% 3.58/0.98  orderings_time:                         0.
% 3.58/0.98  out_proof_time:                         0.012
% 3.58/0.98  total_time:                             0.242
% 3.58/0.98  num_of_symbols:                         51
% 3.58/0.98  num_of_terms:                           12344
% 3.58/0.98  
% 3.58/0.98  ------ Preprocessing
% 3.58/0.98  
% 3.58/0.98  num_of_splits:                          0
% 3.58/0.98  num_of_split_atoms:                     0
% 3.58/0.98  num_of_reused_defs:                     0
% 3.58/0.98  num_eq_ax_congr_red:                    30
% 3.58/0.98  num_of_sem_filtered_clauses:            1
% 3.58/0.98  num_of_subtypes:                        0
% 3.58/0.98  monotx_restored_types:                  0
% 3.58/0.98  sat_num_of_epr_types:                   0
% 3.58/0.98  sat_num_of_non_cyclic_types:            0
% 3.58/0.98  sat_guarded_non_collapsed_types:        0
% 3.58/0.98  num_pure_diseq_elim:                    0
% 3.58/0.98  simp_replaced_by:                       0
% 3.58/0.98  res_preprocessed:                       82
% 3.58/0.98  prep_upred:                             0
% 3.58/0.98  prep_unflattend:                        0
% 3.58/0.98  smt_new_axioms:                         0
% 3.58/0.98  pred_elim_cands:                        3
% 3.58/0.98  pred_elim:                              0
% 3.58/0.98  pred_elim_cl:                           0
% 3.58/0.98  pred_elim_cycles:                       1
% 3.58/0.98  merged_defs:                            0
% 3.58/0.98  merged_defs_ncl:                        0
% 3.58/0.98  bin_hyper_res:                          0
% 3.58/0.98  prep_cycles:                            3
% 3.58/0.98  pred_elim_time:                         0.
% 3.58/0.98  splitting_time:                         0.
% 3.58/0.98  sem_filter_time:                        0.
% 3.58/0.98  monotx_time:                            0.
% 3.58/0.98  subtype_inf_time:                       0.
% 3.58/0.98  
% 3.58/0.98  ------ Problem properties
% 3.58/0.98  
% 3.58/0.98  clauses:                                21
% 3.58/0.98  conjectures:                            6
% 3.58/0.98  epr:                                    1
% 3.58/0.98  horn:                                   16
% 3.58/0.98  ground:                                 5
% 3.58/0.98  unary:                                  3
% 3.58/0.98  binary:                                 6
% 3.58/0.98  lits:                                   69
% 3.58/0.98  lits_eq:                                4
% 3.58/0.98  fd_pure:                                0
% 3.58/0.98  fd_pseudo:                              0
% 3.58/0.98  fd_cond:                                0
% 3.58/0.98  fd_pseudo_cond:                         3
% 3.58/0.98  ac_symbols:                             0
% 3.58/0.98  
% 3.58/0.98  ------ Propositional Solver
% 3.58/0.98  
% 3.58/0.98  prop_solver_calls:                      24
% 3.58/0.98  prop_fast_solver_calls:                 1081
% 3.58/0.98  smt_solver_calls:                       0
% 3.58/0.98  smt_fast_solver_calls:                  0
% 3.58/0.98  prop_num_of_clauses:                    3529
% 3.58/0.98  prop_preprocess_simplified:             6945
% 3.58/0.98  prop_fo_subsumed:                       59
% 3.58/0.98  prop_solver_time:                       0.
% 3.58/0.98  smt_solver_time:                        0.
% 3.58/0.98  smt_fast_solver_time:                   0.
% 3.58/0.98  prop_fast_solver_time:                  0.
% 3.58/0.98  prop_unsat_core_time:                   0.
% 3.58/0.98  
% 3.58/0.98  ------ QBF
% 3.58/0.98  
% 3.58/0.98  qbf_q_res:                              0
% 3.58/0.98  qbf_num_tautologies:                    0
% 3.58/0.98  qbf_prep_cycles:                        0
% 3.58/0.98  
% 3.58/0.98  ------ BMC1
% 3.58/0.98  
% 3.58/0.98  bmc1_current_bound:                     -1
% 3.58/0.98  bmc1_last_solved_bound:                 -1
% 3.58/0.98  bmc1_unsat_core_size:                   -1
% 3.58/0.98  bmc1_unsat_core_parents_size:           -1
% 3.58/0.98  bmc1_merge_next_fun:                    0
% 3.58/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.58/0.98  
% 3.58/0.98  ------ Instantiation
% 3.58/0.98  
% 3.58/0.98  inst_num_of_clauses:                    676
% 3.58/0.98  inst_num_in_passive:                    169
% 3.58/0.98  inst_num_in_active:                     487
% 3.58/0.98  inst_num_in_unprocessed:                20
% 3.58/0.98  inst_num_of_loops:                      550
% 3.58/0.98  inst_num_of_learning_restarts:          0
% 3.58/0.98  inst_num_moves_active_passive:          60
% 3.58/0.98  inst_lit_activity:                      0
% 3.58/0.98  inst_lit_activity_moves:                0
% 3.58/0.98  inst_num_tautologies:                   0
% 3.58/0.98  inst_num_prop_implied:                  0
% 3.58/0.98  inst_num_existing_simplified:           0
% 3.58/0.98  inst_num_eq_res_simplified:             0
% 3.58/0.98  inst_num_child_elim:                    0
% 3.58/0.98  inst_num_of_dismatching_blockings:      96
% 3.58/0.98  inst_num_of_non_proper_insts:           296
% 3.58/0.98  inst_num_of_duplicates:                 0
% 3.58/0.98  inst_inst_num_from_inst_to_res:         0
% 3.58/0.98  inst_dismatching_checking_time:         0.
% 3.58/0.98  
% 3.58/0.98  ------ Resolution
% 3.58/0.98  
% 3.58/0.98  res_num_of_clauses:                     0
% 3.58/0.98  res_num_in_passive:                     0
% 3.58/0.98  res_num_in_active:                      0
% 3.58/0.98  res_num_of_loops:                       85
% 3.58/0.98  res_forward_subset_subsumed:            16
% 3.58/0.98  res_backward_subset_subsumed:           0
% 3.58/0.98  res_forward_subsumed:                   0
% 3.58/0.98  res_backward_subsumed:                  0
% 3.58/0.98  res_forward_subsumption_resolution:     0
% 3.58/0.98  res_backward_subsumption_resolution:    0
% 3.58/0.98  res_clause_to_clause_subsumption:       1058
% 3.58/0.98  res_orphan_elimination:                 0
% 3.58/0.98  res_tautology_del:                      25
% 3.58/0.98  res_num_eq_res_simplified:              0
% 3.58/0.98  res_num_sel_changes:                    0
% 3.58/0.98  res_moves_from_active_to_pass:          0
% 3.58/0.98  
% 3.58/0.98  ------ Superposition
% 3.58/0.98  
% 3.58/0.98  sup_time_total:                         0.
% 3.58/0.98  sup_time_generating:                    0.
% 3.58/0.98  sup_time_sim_full:                      0.
% 3.58/0.98  sup_time_sim_immed:                     0.
% 3.58/0.98  
% 3.58/0.98  sup_num_of_clauses:                     321
% 3.58/0.98  sup_num_in_active:                      76
% 3.58/0.98  sup_num_in_passive:                     245
% 3.58/0.98  sup_num_of_loops:                       108
% 3.58/0.98  sup_fw_superposition:                   223
% 3.58/0.98  sup_bw_superposition:                   164
% 3.58/0.98  sup_immediate_simplified:               26
% 3.58/0.98  sup_given_eliminated:                   1
% 3.58/0.98  comparisons_done:                       0
% 3.58/0.98  comparisons_avoided:                    0
% 3.58/0.98  
% 3.58/0.98  ------ Simplifications
% 3.58/0.98  
% 3.58/0.98  
% 3.58/0.98  sim_fw_subset_subsumed:                 6
% 3.58/0.98  sim_bw_subset_subsumed:                 21
% 3.58/0.98  sim_fw_subsumed:                        20
% 3.58/0.98  sim_bw_subsumed:                        25
% 3.58/0.98  sim_fw_subsumption_res:                 0
% 3.58/0.98  sim_bw_subsumption_res:                 0
% 3.58/0.98  sim_tautology_del:                      6
% 3.58/0.98  sim_eq_tautology_del:                   0
% 3.58/0.98  sim_eq_res_simp:                        0
% 3.58/0.98  sim_fw_demodulated:                     0
% 3.58/0.98  sim_bw_demodulated:                     4
% 3.58/0.98  sim_light_normalised:                   3
% 3.58/0.98  sim_joinable_taut:                      0
% 3.58/0.98  sim_joinable_simp:                      0
% 3.58/0.98  sim_ac_normalised:                      0
% 3.58/0.98  sim_smt_subsumption:                    0
% 3.58/0.98  
%------------------------------------------------------------------------------

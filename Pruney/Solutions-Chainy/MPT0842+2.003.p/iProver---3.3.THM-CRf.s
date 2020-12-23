%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:02 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 744 expanded)
%              Number of clauses        :   59 ( 226 expanded)
%              Number of leaves         :   14 ( 164 expanded)
%              Depth                    :   22
%              Number of atoms          :  417 (4312 expanded)
%              Number of equality atoms :  105 ( 317 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f12,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
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
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
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
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ? [X0,X1,X2,X3] :
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
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X4,X2,X3,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X4,X6),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK6,X1)
        & r2_hidden(k4_tarski(X4,sK6),X3)
        & m1_subset_1(sK6,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
              | ~ r2_hidden(k4_tarski(sK5,X5),X3)
              | ~ m1_subset_1(X5,X2) )
          | ~ r2_hidden(sK5,k8_relset_1(X0,X2,X3,X1)) )
        & ( ? [X6] :
              ( r2_hidden(X6,X1)
              & r2_hidden(k4_tarski(sK5,X6),X3)
              & m1_subset_1(X6,X2) )
          | r2_hidden(sK5,k8_relset_1(X0,X2,X3,X1)) )
        & m1_subset_1(sK5,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
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
                ( ~ r2_hidden(X5,sK2)
                | ~ r2_hidden(k4_tarski(X4,X5),sK4)
                | ~ m1_subset_1(X5,sK3) )
            | ~ r2_hidden(X4,k8_relset_1(sK1,sK3,sK4,sK2)) )
          & ( ? [X6] :
                ( r2_hidden(X6,sK2)
                & r2_hidden(k4_tarski(X4,X6),sK4)
                & m1_subset_1(X6,sK3) )
            | r2_hidden(X4,k8_relset_1(sK1,sK3,sK4,sK2)) )
          & m1_subset_1(X4,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( ! [X5] :
          ( ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(k4_tarski(sK5,X5),sK4)
          | ~ m1_subset_1(X5,sK3) )
      | ~ r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) )
    & ( ( r2_hidden(sK6,sK2)
        & r2_hidden(k4_tarski(sK5,sK6),sK4)
        & m1_subset_1(sK6,sK3) )
      | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) )
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f35,f38,f37,f36])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK4)
    | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK0(X0,X1,X2)),X2)
        & r2_hidden(sK0(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK0(X0,X1,X2)),X2)
            & r2_hidden(sK0(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK0(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(k4_tarski(sK5,X5),sK4)
      | ~ m1_subset_1(X5,sK3)
      | ~ r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,
    ( r2_hidden(sK6,sK2)
    | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1519,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1525,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1943,plain,
    ( k8_relset_1(sK1,sK3,sK4,X0) = k10_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1519,c_1525])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(k4_tarski(sK5,sK6),sK4)
    | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1522,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK4) = iProver_top
    | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2115,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK4) = iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1943,c_1522])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1535,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
    | r2_hidden(X0,k2_relat_1(X3)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1531,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1632,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1535,c_1531])).

cnf(c_3302,plain,
    ( r2_hidden(sK6,X0) != iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,X0)) = iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,sK2)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2115,c_1632])).

cnf(c_22,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1682,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1683,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1682])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK0(X0,X2,X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1533,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK0(X0,X2,X1)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_14,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_250,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_14,c_2])).

cnf(c_260,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_250,c_13])).

cnf(c_12,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_270,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X2)) = X0 ),
    inference(resolution,[status(thm)],[c_260,c_12])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relat_1(X0,k6_relat_1(X2)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_270,c_13])).

cnf(c_1518,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_274])).

cnf(c_1885,plain,
    ( k5_relat_1(sK4,k6_relat_1(sK3)) = sK4 ),
    inference(superposition,[status(thm)],[c_1519,c_1518])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k5_relat_1(X3,k6_relat_1(X1)))
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1527,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k5_relat_1(X3,k6_relat_1(X1))) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2259,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1885,c_1527])).

cnf(c_2546,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2259,c_22,c_1683])).

cnf(c_2547,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_2546])).

cnf(c_2921,plain,
    ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK4),sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1533,c_2547])).

cnf(c_3248,plain,
    ( r2_hidden(sK0(X0,X1,sK4),sK3) = iProver_top
    | r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2921,c_22,c_1683])).

cnf(c_3249,plain,
    ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK4),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3248])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1536,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3256,plain,
    ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
    | m1_subset_1(sK0(X0,X1,sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3249,c_1536])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1534,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(k4_tarski(sK5,X0),sK4)
    | ~ r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2))
    | ~ m1_subset_1(X0,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1524,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k4_tarski(sK5,X0),sK4) != iProver_top
    | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2118,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k4_tarski(sK5,X0),sK4) != iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1943,c_1524])).

cnf(c_2917,plain,
    ( r2_hidden(sK0(sK5,X0,sK4),sK2) != iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,X0)) != iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
    | m1_subset_1(sK0(sK5,X0,sK4),sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1533,c_2118])).

cnf(c_3187,plain,
    ( m1_subset_1(sK0(sK5,X0,sK4),sK3) != iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,X0)) != iProver_top
    | r2_hidden(sK0(sK5,X0,sK4),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2917,c_22,c_1683])).

cnf(c_3188,plain,
    ( r2_hidden(sK0(sK5,X0,sK4),sK2) != iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,X0)) != iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
    | m1_subset_1(sK0(sK5,X0,sK4),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3187])).

cnf(c_3197,plain,
    ( r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
    | m1_subset_1(sK0(sK5,sK2,sK4),sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1534,c_3188])).

cnf(c_3283,plain,
    ( m1_subset_1(sK0(sK5,sK2,sK4),sK3) != iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3197,c_22,c_1683])).

cnf(c_3284,plain,
    ( r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
    | m1_subset_1(sK0(sK5,sK2,sK4),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3283])).

cnf(c_3412,plain,
    ( r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3256,c_3284])).

cnf(c_3415,plain,
    ( r2_hidden(sK6,X0) != iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3302,c_22,c_1683,c_3412])).

cnf(c_4048,plain,
    ( r2_hidden(sK6,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3415,c_3412])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK6,sK2)
    | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1523,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2116,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1943,c_1523])).

cnf(c_4053,plain,
    ( r2_hidden(sK6,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2116,c_3412])).

cnf(c_4061,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4048,c_4053])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:17:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.35/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/0.98  
% 2.35/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.35/0.98  
% 2.35/0.98  ------  iProver source info
% 2.35/0.98  
% 2.35/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.35/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.35/0.98  git: non_committed_changes: false
% 2.35/0.98  git: last_make_outside_of_git: false
% 2.35/0.98  
% 2.35/0.98  ------ 
% 2.35/0.98  
% 2.35/0.98  ------ Input Options
% 2.35/0.98  
% 2.35/0.98  --out_options                           all
% 2.35/0.98  --tptp_safe_out                         true
% 2.35/0.98  --problem_path                          ""
% 2.35/0.98  --include_path                          ""
% 2.35/0.98  --clausifier                            res/vclausify_rel
% 2.35/0.98  --clausifier_options                    --mode clausify
% 2.35/0.98  --stdin                                 false
% 2.35/0.98  --stats_out                             all
% 2.35/0.98  
% 2.35/0.98  ------ General Options
% 2.35/0.98  
% 2.35/0.98  --fof                                   false
% 2.35/0.98  --time_out_real                         305.
% 2.35/0.98  --time_out_virtual                      -1.
% 2.35/0.98  --symbol_type_check                     false
% 2.35/0.98  --clausify_out                          false
% 2.35/0.98  --sig_cnt_out                           false
% 2.35/0.98  --trig_cnt_out                          false
% 2.35/0.98  --trig_cnt_out_tolerance                1.
% 2.35/0.98  --trig_cnt_out_sk_spl                   false
% 2.35/0.98  --abstr_cl_out                          false
% 2.35/0.98  
% 2.35/0.98  ------ Global Options
% 2.35/0.98  
% 2.35/0.98  --schedule                              default
% 2.35/0.98  --add_important_lit                     false
% 2.35/0.98  --prop_solver_per_cl                    1000
% 2.35/0.98  --min_unsat_core                        false
% 2.35/0.98  --soft_assumptions                      false
% 2.35/0.98  --soft_lemma_size                       3
% 2.35/0.98  --prop_impl_unit_size                   0
% 2.35/0.98  --prop_impl_unit                        []
% 2.35/0.98  --share_sel_clauses                     true
% 2.35/0.98  --reset_solvers                         false
% 2.35/0.98  --bc_imp_inh                            [conj_cone]
% 2.35/0.98  --conj_cone_tolerance                   3.
% 2.35/0.98  --extra_neg_conj                        none
% 2.35/0.98  --large_theory_mode                     true
% 2.35/0.98  --prolific_symb_bound                   200
% 2.35/0.98  --lt_threshold                          2000
% 2.35/0.98  --clause_weak_htbl                      true
% 2.35/0.98  --gc_record_bc_elim                     false
% 2.35/0.98  
% 2.35/0.98  ------ Preprocessing Options
% 2.35/0.98  
% 2.35/0.98  --preprocessing_flag                    true
% 2.35/0.98  --time_out_prep_mult                    0.1
% 2.35/0.98  --splitting_mode                        input
% 2.35/0.98  --splitting_grd                         true
% 2.35/0.98  --splitting_cvd                         false
% 2.35/0.98  --splitting_cvd_svl                     false
% 2.35/0.98  --splitting_nvd                         32
% 2.35/0.98  --sub_typing                            true
% 2.35/0.98  --prep_gs_sim                           true
% 2.35/0.98  --prep_unflatten                        true
% 2.35/0.98  --prep_res_sim                          true
% 2.35/0.98  --prep_upred                            true
% 2.35/0.98  --prep_sem_filter                       exhaustive
% 2.35/0.98  --prep_sem_filter_out                   false
% 2.35/0.98  --pred_elim                             true
% 2.35/0.98  --res_sim_input                         true
% 2.35/0.98  --eq_ax_congr_red                       true
% 2.35/0.98  --pure_diseq_elim                       true
% 2.35/0.98  --brand_transform                       false
% 2.35/0.98  --non_eq_to_eq                          false
% 2.35/0.98  --prep_def_merge                        true
% 2.35/0.98  --prep_def_merge_prop_impl              false
% 2.35/0.98  --prep_def_merge_mbd                    true
% 2.35/0.98  --prep_def_merge_tr_red                 false
% 2.35/0.98  --prep_def_merge_tr_cl                  false
% 2.35/0.98  --smt_preprocessing                     true
% 2.35/0.98  --smt_ac_axioms                         fast
% 2.35/0.98  --preprocessed_out                      false
% 2.35/0.98  --preprocessed_stats                    false
% 2.35/0.98  
% 2.35/0.98  ------ Abstraction refinement Options
% 2.35/0.98  
% 2.35/0.98  --abstr_ref                             []
% 2.35/0.98  --abstr_ref_prep                        false
% 2.35/0.98  --abstr_ref_until_sat                   false
% 2.35/0.98  --abstr_ref_sig_restrict                funpre
% 2.35/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.35/0.98  --abstr_ref_under                       []
% 2.35/0.98  
% 2.35/0.98  ------ SAT Options
% 2.35/0.98  
% 2.35/0.98  --sat_mode                              false
% 2.35/0.98  --sat_fm_restart_options                ""
% 2.35/0.98  --sat_gr_def                            false
% 2.35/0.98  --sat_epr_types                         true
% 2.35/0.98  --sat_non_cyclic_types                  false
% 2.35/0.98  --sat_finite_models                     false
% 2.35/0.98  --sat_fm_lemmas                         false
% 2.35/0.98  --sat_fm_prep                           false
% 2.35/0.98  --sat_fm_uc_incr                        true
% 2.35/0.98  --sat_out_model                         small
% 2.35/0.98  --sat_out_clauses                       false
% 2.35/0.98  
% 2.35/0.98  ------ QBF Options
% 2.35/0.98  
% 2.35/0.98  --qbf_mode                              false
% 2.35/0.98  --qbf_elim_univ                         false
% 2.35/0.98  --qbf_dom_inst                          none
% 2.35/0.98  --qbf_dom_pre_inst                      false
% 2.35/0.98  --qbf_sk_in                             false
% 2.35/0.98  --qbf_pred_elim                         true
% 2.35/0.98  --qbf_split                             512
% 2.35/0.98  
% 2.35/0.98  ------ BMC1 Options
% 2.35/0.98  
% 2.35/0.98  --bmc1_incremental                      false
% 2.35/0.98  --bmc1_axioms                           reachable_all
% 2.35/0.98  --bmc1_min_bound                        0
% 2.35/0.98  --bmc1_max_bound                        -1
% 2.35/0.98  --bmc1_max_bound_default                -1
% 2.35/0.98  --bmc1_symbol_reachability              true
% 2.35/0.98  --bmc1_property_lemmas                  false
% 2.35/0.98  --bmc1_k_induction                      false
% 2.35/0.98  --bmc1_non_equiv_states                 false
% 2.35/0.98  --bmc1_deadlock                         false
% 2.35/0.98  --bmc1_ucm                              false
% 2.35/0.98  --bmc1_add_unsat_core                   none
% 2.35/0.98  --bmc1_unsat_core_children              false
% 2.35/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.35/0.98  --bmc1_out_stat                         full
% 2.35/0.98  --bmc1_ground_init                      false
% 2.35/0.98  --bmc1_pre_inst_next_state              false
% 2.35/0.98  --bmc1_pre_inst_state                   false
% 2.35/0.98  --bmc1_pre_inst_reach_state             false
% 2.35/0.98  --bmc1_out_unsat_core                   false
% 2.35/0.98  --bmc1_aig_witness_out                  false
% 2.35/0.98  --bmc1_verbose                          false
% 2.35/0.98  --bmc1_dump_clauses_tptp                false
% 2.35/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.35/0.98  --bmc1_dump_file                        -
% 2.35/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.35/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.35/0.98  --bmc1_ucm_extend_mode                  1
% 2.35/0.98  --bmc1_ucm_init_mode                    2
% 2.35/0.98  --bmc1_ucm_cone_mode                    none
% 2.35/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.35/0.98  --bmc1_ucm_relax_model                  4
% 2.35/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.35/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.35/0.98  --bmc1_ucm_layered_model                none
% 2.35/0.98  --bmc1_ucm_max_lemma_size               10
% 2.35/0.98  
% 2.35/0.98  ------ AIG Options
% 2.35/0.98  
% 2.35/0.98  --aig_mode                              false
% 2.35/0.98  
% 2.35/0.98  ------ Instantiation Options
% 2.35/0.98  
% 2.35/0.98  --instantiation_flag                    true
% 2.35/0.98  --inst_sos_flag                         false
% 2.35/0.98  --inst_sos_phase                        true
% 2.35/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.35/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.35/0.98  --inst_lit_sel_side                     num_symb
% 2.35/0.98  --inst_solver_per_active                1400
% 2.35/0.98  --inst_solver_calls_frac                1.
% 2.35/0.98  --inst_passive_queue_type               priority_queues
% 2.35/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.35/0.98  --inst_passive_queues_freq              [25;2]
% 2.35/0.98  --inst_dismatching                      true
% 2.35/0.98  --inst_eager_unprocessed_to_passive     true
% 2.35/0.98  --inst_prop_sim_given                   true
% 2.35/0.98  --inst_prop_sim_new                     false
% 2.35/0.98  --inst_subs_new                         false
% 2.35/0.98  --inst_eq_res_simp                      false
% 2.35/0.98  --inst_subs_given                       false
% 2.35/0.98  --inst_orphan_elimination               true
% 2.35/0.98  --inst_learning_loop_flag               true
% 2.35/0.98  --inst_learning_start                   3000
% 2.35/0.98  --inst_learning_factor                  2
% 2.35/0.98  --inst_start_prop_sim_after_learn       3
% 2.35/0.98  --inst_sel_renew                        solver
% 2.35/0.98  --inst_lit_activity_flag                true
% 2.35/0.98  --inst_restr_to_given                   false
% 2.35/0.98  --inst_activity_threshold               500
% 2.35/0.98  --inst_out_proof                        true
% 2.35/0.98  
% 2.35/0.98  ------ Resolution Options
% 2.35/0.98  
% 2.35/0.98  --resolution_flag                       true
% 2.35/0.98  --res_lit_sel                           adaptive
% 2.35/0.98  --res_lit_sel_side                      none
% 2.35/0.98  --res_ordering                          kbo
% 2.35/0.98  --res_to_prop_solver                    active
% 2.35/0.98  --res_prop_simpl_new                    false
% 2.35/0.98  --res_prop_simpl_given                  true
% 2.35/0.98  --res_passive_queue_type                priority_queues
% 2.35/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.35/0.98  --res_passive_queues_freq               [15;5]
% 2.35/0.98  --res_forward_subs                      full
% 2.35/0.98  --res_backward_subs                     full
% 2.35/0.98  --res_forward_subs_resolution           true
% 2.35/0.98  --res_backward_subs_resolution          true
% 2.35/0.98  --res_orphan_elimination                true
% 2.35/0.98  --res_time_limit                        2.
% 2.35/0.98  --res_out_proof                         true
% 2.35/0.98  
% 2.35/0.98  ------ Superposition Options
% 2.35/0.98  
% 2.35/0.98  --superposition_flag                    true
% 2.35/0.98  --sup_passive_queue_type                priority_queues
% 2.35/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.35/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.35/0.98  --demod_completeness_check              fast
% 2.35/0.98  --demod_use_ground                      true
% 2.35/0.98  --sup_to_prop_solver                    passive
% 2.35/0.98  --sup_prop_simpl_new                    true
% 2.35/0.98  --sup_prop_simpl_given                  true
% 2.35/0.98  --sup_fun_splitting                     false
% 2.35/0.98  --sup_smt_interval                      50000
% 2.35/0.98  
% 2.35/0.98  ------ Superposition Simplification Setup
% 2.35/0.98  
% 2.35/0.98  --sup_indices_passive                   []
% 2.35/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.35/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.98  --sup_full_bw                           [BwDemod]
% 2.35/0.98  --sup_immed_triv                        [TrivRules]
% 2.35/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.35/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.98  --sup_immed_bw_main                     []
% 2.35/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.35/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.98  
% 2.35/0.98  ------ Combination Options
% 2.35/0.98  
% 2.35/0.98  --comb_res_mult                         3
% 2.35/0.98  --comb_sup_mult                         2
% 2.35/0.98  --comb_inst_mult                        10
% 2.35/0.98  
% 2.35/0.98  ------ Debug Options
% 2.35/0.98  
% 2.35/0.98  --dbg_backtrace                         false
% 2.35/0.98  --dbg_dump_prop_clauses                 false
% 2.35/0.98  --dbg_dump_prop_clauses_file            -
% 2.35/0.98  --dbg_out_stat                          false
% 2.35/0.98  ------ Parsing...
% 2.35/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.35/0.98  
% 2.35/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.35/0.98  
% 2.35/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.35/0.98  
% 2.35/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.35/0.98  ------ Proving...
% 2.35/0.98  ------ Problem Properties 
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  clauses                                 19
% 2.35/0.98  conjectures                             6
% 2.35/0.98  EPR                                     2
% 2.35/0.98  Horn                                    16
% 2.35/0.98  unary                                   2
% 2.35/0.98  binary                                  7
% 2.35/0.98  lits                                    50
% 2.35/0.98  lits eq                                 2
% 2.35/0.98  fd_pure                                 0
% 2.35/0.98  fd_pseudo                               0
% 2.35/0.98  fd_cond                                 0
% 2.35/0.98  fd_pseudo_cond                          0
% 2.35/0.98  AC symbols                              0
% 2.35/0.98  
% 2.35/0.98  ------ Schedule dynamic 5 is on 
% 2.35/0.98  
% 2.35/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  ------ 
% 2.35/0.98  Current options:
% 2.35/0.98  ------ 
% 2.35/0.98  
% 2.35/0.98  ------ Input Options
% 2.35/0.98  
% 2.35/0.98  --out_options                           all
% 2.35/0.98  --tptp_safe_out                         true
% 2.35/0.98  --problem_path                          ""
% 2.35/0.98  --include_path                          ""
% 2.35/0.98  --clausifier                            res/vclausify_rel
% 2.35/0.98  --clausifier_options                    --mode clausify
% 2.35/0.98  --stdin                                 false
% 2.35/0.98  --stats_out                             all
% 2.35/0.98  
% 2.35/0.98  ------ General Options
% 2.35/0.98  
% 2.35/0.98  --fof                                   false
% 2.35/0.98  --time_out_real                         305.
% 2.35/0.98  --time_out_virtual                      -1.
% 2.35/0.98  --symbol_type_check                     false
% 2.35/0.98  --clausify_out                          false
% 2.35/0.98  --sig_cnt_out                           false
% 2.35/0.98  --trig_cnt_out                          false
% 2.35/0.98  --trig_cnt_out_tolerance                1.
% 2.35/0.98  --trig_cnt_out_sk_spl                   false
% 2.35/0.98  --abstr_cl_out                          false
% 2.35/0.98  
% 2.35/0.98  ------ Global Options
% 2.35/0.98  
% 2.35/0.98  --schedule                              default
% 2.35/0.98  --add_important_lit                     false
% 2.35/0.98  --prop_solver_per_cl                    1000
% 2.35/0.98  --min_unsat_core                        false
% 2.35/0.98  --soft_assumptions                      false
% 2.35/0.98  --soft_lemma_size                       3
% 2.35/0.98  --prop_impl_unit_size                   0
% 2.35/0.98  --prop_impl_unit                        []
% 2.35/0.98  --share_sel_clauses                     true
% 2.35/0.98  --reset_solvers                         false
% 2.35/0.98  --bc_imp_inh                            [conj_cone]
% 2.35/0.98  --conj_cone_tolerance                   3.
% 2.35/0.98  --extra_neg_conj                        none
% 2.35/0.98  --large_theory_mode                     true
% 2.35/0.98  --prolific_symb_bound                   200
% 2.35/0.98  --lt_threshold                          2000
% 2.35/0.98  --clause_weak_htbl                      true
% 2.35/0.98  --gc_record_bc_elim                     false
% 2.35/0.98  
% 2.35/0.98  ------ Preprocessing Options
% 2.35/0.98  
% 2.35/0.98  --preprocessing_flag                    true
% 2.35/0.98  --time_out_prep_mult                    0.1
% 2.35/0.98  --splitting_mode                        input
% 2.35/0.98  --splitting_grd                         true
% 2.35/0.98  --splitting_cvd                         false
% 2.35/0.98  --splitting_cvd_svl                     false
% 2.35/0.98  --splitting_nvd                         32
% 2.35/0.98  --sub_typing                            true
% 2.35/0.98  --prep_gs_sim                           true
% 2.35/0.98  --prep_unflatten                        true
% 2.35/0.98  --prep_res_sim                          true
% 2.35/0.98  --prep_upred                            true
% 2.35/0.98  --prep_sem_filter                       exhaustive
% 2.35/0.98  --prep_sem_filter_out                   false
% 2.35/0.98  --pred_elim                             true
% 2.35/0.98  --res_sim_input                         true
% 2.35/0.98  --eq_ax_congr_red                       true
% 2.35/0.98  --pure_diseq_elim                       true
% 2.35/0.98  --brand_transform                       false
% 2.35/0.98  --non_eq_to_eq                          false
% 2.35/0.98  --prep_def_merge                        true
% 2.35/0.98  --prep_def_merge_prop_impl              false
% 2.35/0.98  --prep_def_merge_mbd                    true
% 2.35/0.98  --prep_def_merge_tr_red                 false
% 2.35/0.98  --prep_def_merge_tr_cl                  false
% 2.35/0.98  --smt_preprocessing                     true
% 2.35/0.98  --smt_ac_axioms                         fast
% 2.35/0.98  --preprocessed_out                      false
% 2.35/0.98  --preprocessed_stats                    false
% 2.35/0.98  
% 2.35/0.98  ------ Abstraction refinement Options
% 2.35/0.98  
% 2.35/0.98  --abstr_ref                             []
% 2.35/0.98  --abstr_ref_prep                        false
% 2.35/0.98  --abstr_ref_until_sat                   false
% 2.35/0.98  --abstr_ref_sig_restrict                funpre
% 2.35/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.35/0.98  --abstr_ref_under                       []
% 2.35/0.98  
% 2.35/0.98  ------ SAT Options
% 2.35/0.98  
% 2.35/0.98  --sat_mode                              false
% 2.35/0.98  --sat_fm_restart_options                ""
% 2.35/0.98  --sat_gr_def                            false
% 2.35/0.98  --sat_epr_types                         true
% 2.35/0.98  --sat_non_cyclic_types                  false
% 2.35/0.98  --sat_finite_models                     false
% 2.35/0.98  --sat_fm_lemmas                         false
% 2.35/0.98  --sat_fm_prep                           false
% 2.35/0.98  --sat_fm_uc_incr                        true
% 2.35/0.98  --sat_out_model                         small
% 2.35/0.98  --sat_out_clauses                       false
% 2.35/0.98  
% 2.35/0.98  ------ QBF Options
% 2.35/0.98  
% 2.35/0.98  --qbf_mode                              false
% 2.35/0.98  --qbf_elim_univ                         false
% 2.35/0.98  --qbf_dom_inst                          none
% 2.35/0.98  --qbf_dom_pre_inst                      false
% 2.35/0.98  --qbf_sk_in                             false
% 2.35/0.98  --qbf_pred_elim                         true
% 2.35/0.98  --qbf_split                             512
% 2.35/0.98  
% 2.35/0.98  ------ BMC1 Options
% 2.35/0.98  
% 2.35/0.98  --bmc1_incremental                      false
% 2.35/0.98  --bmc1_axioms                           reachable_all
% 2.35/0.98  --bmc1_min_bound                        0
% 2.35/0.98  --bmc1_max_bound                        -1
% 2.35/0.98  --bmc1_max_bound_default                -1
% 2.35/0.98  --bmc1_symbol_reachability              true
% 2.35/0.98  --bmc1_property_lemmas                  false
% 2.35/0.98  --bmc1_k_induction                      false
% 2.35/0.98  --bmc1_non_equiv_states                 false
% 2.35/0.98  --bmc1_deadlock                         false
% 2.35/0.98  --bmc1_ucm                              false
% 2.35/0.98  --bmc1_add_unsat_core                   none
% 2.35/0.98  --bmc1_unsat_core_children              false
% 2.35/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.35/0.98  --bmc1_out_stat                         full
% 2.35/0.98  --bmc1_ground_init                      false
% 2.35/0.98  --bmc1_pre_inst_next_state              false
% 2.35/0.98  --bmc1_pre_inst_state                   false
% 2.35/0.98  --bmc1_pre_inst_reach_state             false
% 2.35/0.98  --bmc1_out_unsat_core                   false
% 2.35/0.98  --bmc1_aig_witness_out                  false
% 2.35/0.98  --bmc1_verbose                          false
% 2.35/0.98  --bmc1_dump_clauses_tptp                false
% 2.35/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.35/0.98  --bmc1_dump_file                        -
% 2.35/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.35/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.35/0.98  --bmc1_ucm_extend_mode                  1
% 2.35/0.98  --bmc1_ucm_init_mode                    2
% 2.35/0.98  --bmc1_ucm_cone_mode                    none
% 2.35/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.35/0.98  --bmc1_ucm_relax_model                  4
% 2.35/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.35/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.35/0.98  --bmc1_ucm_layered_model                none
% 2.35/0.98  --bmc1_ucm_max_lemma_size               10
% 2.35/0.98  
% 2.35/0.98  ------ AIG Options
% 2.35/0.98  
% 2.35/0.98  --aig_mode                              false
% 2.35/0.98  
% 2.35/0.98  ------ Instantiation Options
% 2.35/0.98  
% 2.35/0.98  --instantiation_flag                    true
% 2.35/0.98  --inst_sos_flag                         false
% 2.35/0.98  --inst_sos_phase                        true
% 2.35/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.35/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.35/0.98  --inst_lit_sel_side                     none
% 2.35/0.98  --inst_solver_per_active                1400
% 2.35/0.98  --inst_solver_calls_frac                1.
% 2.35/0.98  --inst_passive_queue_type               priority_queues
% 2.35/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.35/0.98  --inst_passive_queues_freq              [25;2]
% 2.35/0.98  --inst_dismatching                      true
% 2.35/0.98  --inst_eager_unprocessed_to_passive     true
% 2.35/0.98  --inst_prop_sim_given                   true
% 2.35/0.98  --inst_prop_sim_new                     false
% 2.35/0.98  --inst_subs_new                         false
% 2.35/0.98  --inst_eq_res_simp                      false
% 2.35/0.98  --inst_subs_given                       false
% 2.35/0.98  --inst_orphan_elimination               true
% 2.35/0.98  --inst_learning_loop_flag               true
% 2.35/0.98  --inst_learning_start                   3000
% 2.35/0.98  --inst_learning_factor                  2
% 2.35/0.98  --inst_start_prop_sim_after_learn       3
% 2.35/0.98  --inst_sel_renew                        solver
% 2.35/0.98  --inst_lit_activity_flag                true
% 2.35/0.98  --inst_restr_to_given                   false
% 2.35/0.98  --inst_activity_threshold               500
% 2.35/0.98  --inst_out_proof                        true
% 2.35/0.98  
% 2.35/0.98  ------ Resolution Options
% 2.35/0.98  
% 2.35/0.98  --resolution_flag                       false
% 2.35/0.98  --res_lit_sel                           adaptive
% 2.35/0.98  --res_lit_sel_side                      none
% 2.35/0.98  --res_ordering                          kbo
% 2.35/0.98  --res_to_prop_solver                    active
% 2.35/0.98  --res_prop_simpl_new                    false
% 2.35/0.98  --res_prop_simpl_given                  true
% 2.35/0.98  --res_passive_queue_type                priority_queues
% 2.35/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.35/0.98  --res_passive_queues_freq               [15;5]
% 2.35/0.98  --res_forward_subs                      full
% 2.35/0.98  --res_backward_subs                     full
% 2.35/0.98  --res_forward_subs_resolution           true
% 2.35/0.98  --res_backward_subs_resolution          true
% 2.35/0.98  --res_orphan_elimination                true
% 2.35/0.98  --res_time_limit                        2.
% 2.35/0.98  --res_out_proof                         true
% 2.35/0.98  
% 2.35/0.98  ------ Superposition Options
% 2.35/0.98  
% 2.35/0.98  --superposition_flag                    true
% 2.35/0.98  --sup_passive_queue_type                priority_queues
% 2.35/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.35/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.35/0.98  --demod_completeness_check              fast
% 2.35/0.98  --demod_use_ground                      true
% 2.35/0.98  --sup_to_prop_solver                    passive
% 2.35/0.98  --sup_prop_simpl_new                    true
% 2.35/0.98  --sup_prop_simpl_given                  true
% 2.35/0.98  --sup_fun_splitting                     false
% 2.35/0.98  --sup_smt_interval                      50000
% 2.35/0.98  
% 2.35/0.98  ------ Superposition Simplification Setup
% 2.35/0.98  
% 2.35/0.98  --sup_indices_passive                   []
% 2.35/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.35/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.98  --sup_full_bw                           [BwDemod]
% 2.35/0.98  --sup_immed_triv                        [TrivRules]
% 2.35/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.35/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.98  --sup_immed_bw_main                     []
% 2.35/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.35/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.98  
% 2.35/0.98  ------ Combination Options
% 2.35/0.98  
% 2.35/0.98  --comb_res_mult                         3
% 2.35/0.98  --comb_sup_mult                         2
% 2.35/0.98  --comb_inst_mult                        10
% 2.35/0.98  
% 2.35/0.98  ------ Debug Options
% 2.35/0.98  
% 2.35/0.98  --dbg_backtrace                         false
% 2.35/0.98  --dbg_dump_prop_clauses                 false
% 2.35/0.98  --dbg_dump_prop_clauses_file            -
% 2.35/0.98  --dbg_out_stat                          false
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  ------ Proving...
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  % SZS status Theorem for theBenchmark.p
% 2.35/0.98  
% 2.35/0.98   Resolution empty clause
% 2.35/0.98  
% 2.35/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.35/0.98  
% 2.35/0.98  fof(f10,conjecture,(
% 2.35/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f11,negated_conjecture,(
% 2.35/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 2.35/0.98    inference(negated_conjecture,[],[f10])).
% 2.35/0.98  
% 2.35/0.98  fof(f12,plain,(
% 2.35/0.98    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)))))),
% 2.35/0.98    inference(pure_predicate_removal,[],[f11])).
% 2.35/0.98  
% 2.35/0.98  fof(f25,plain,(
% 2.35/0.98    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.35/0.98    inference(ennf_transformation,[],[f12])).
% 2.35/0.98  
% 2.35/0.98  fof(f33,plain,(
% 2.35/0.98    ? [X0,X1,X2,X3] : (? [X4] : (((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.35/0.98    inference(nnf_transformation,[],[f25])).
% 2.35/0.98  
% 2.35/0.98  fof(f34,plain,(
% 2.35/0.98    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.35/0.98    inference(flattening,[],[f33])).
% 2.35/0.98  
% 2.35/0.98  fof(f35,plain,(
% 2.35/0.98    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.35/0.98    inference(rectify,[],[f34])).
% 2.35/0.98  
% 2.35/0.98  fof(f38,plain,(
% 2.35/0.98    ( ! [X4,X2,X3,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK6,X1) & r2_hidden(k4_tarski(X4,sK6),X3) & m1_subset_1(sK6,X2))) )),
% 2.35/0.98    introduced(choice_axiom,[])).
% 2.35/0.98  
% 2.35/0.98  fof(f37,plain,(
% 2.35/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) => ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(sK5,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(sK5,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(sK5,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(sK5,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(sK5,X0))) )),
% 2.35/0.98    introduced(choice_axiom,[])).
% 2.35/0.98  
% 2.35/0.98  fof(f36,plain,(
% 2.35/0.98    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (? [X4] : ((! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(k4_tarski(X4,X5),sK4) | ~m1_subset_1(X5,sK3)) | ~r2_hidden(X4,k8_relset_1(sK1,sK3,sK4,sK2))) & (? [X6] : (r2_hidden(X6,sK2) & r2_hidden(k4_tarski(X4,X6),sK4) & m1_subset_1(X6,sK3)) | r2_hidden(X4,k8_relset_1(sK1,sK3,sK4,sK2))) & m1_subset_1(X4,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))))),
% 2.35/0.98    introduced(choice_axiom,[])).
% 2.35/0.98  
% 2.35/0.98  fof(f39,plain,(
% 2.35/0.98    ((! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(k4_tarski(sK5,X5),sK4) | ~m1_subset_1(X5,sK3)) | ~r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2))) & ((r2_hidden(sK6,sK2) & r2_hidden(k4_tarski(sK5,sK6),sK4) & m1_subset_1(sK6,sK3)) | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2))) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 2.35/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f35,f38,f37,f36])).
% 2.35/0.98  
% 2.35/0.98  fof(f56,plain,(
% 2.35/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 2.35/0.98    inference(cnf_transformation,[],[f39])).
% 2.35/0.98  
% 2.35/0.98  fof(f9,axiom,(
% 2.35/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f24,plain,(
% 2.35/0.98    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.98    inference(ennf_transformation,[],[f9])).
% 2.35/0.98  
% 2.35/0.98  fof(f55,plain,(
% 2.35/0.98    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.35/0.98    inference(cnf_transformation,[],[f24])).
% 2.35/0.98  
% 2.35/0.98  fof(f59,plain,(
% 2.35/0.98    r2_hidden(k4_tarski(sK5,sK6),sK4) | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2))),
% 2.35/0.98    inference(cnf_transformation,[],[f39])).
% 2.35/0.98  
% 2.35/0.98  fof(f3,axiom,(
% 2.35/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f16,plain,(
% 2.35/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.35/0.98    inference(ennf_transformation,[],[f3])).
% 2.35/0.98  
% 2.35/0.98  fof(f27,plain,(
% 2.35/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.35/0.98    inference(nnf_transformation,[],[f16])).
% 2.35/0.98  
% 2.35/0.98  fof(f28,plain,(
% 2.35/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.35/0.98    inference(rectify,[],[f27])).
% 2.35/0.98  
% 2.35/0.98  fof(f29,plain,(
% 2.35/0.98    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK0(X0,X1,X2)),X2) & r2_hidden(sK0(X0,X1,X2),k2_relat_1(X2))))),
% 2.35/0.98    introduced(choice_axiom,[])).
% 2.35/0.98  
% 2.35/0.98  fof(f30,plain,(
% 2.35/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK0(X0,X1,X2)),X2) & r2_hidden(sK0(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.35/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 2.35/0.98  
% 2.35/0.98  fof(f46,plain,(
% 2.35/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f30])).
% 2.35/0.98  
% 2.35/0.98  fof(f4,axiom,(
% 2.35/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f17,plain,(
% 2.35/0.98    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 2.35/0.98    inference(ennf_transformation,[],[f4])).
% 2.35/0.98  
% 2.35/0.98  fof(f18,plain,(
% 2.35/0.98    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 2.35/0.98    inference(flattening,[],[f17])).
% 2.35/0.98  
% 2.35/0.98  fof(f48,plain,(
% 2.35/0.98    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f18])).
% 2.35/0.98  
% 2.35/0.98  fof(f7,axiom,(
% 2.35/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f22,plain,(
% 2.35/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.98    inference(ennf_transformation,[],[f7])).
% 2.35/0.98  
% 2.35/0.98  fof(f53,plain,(
% 2.35/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.35/0.98    inference(cnf_transformation,[],[f22])).
% 2.35/0.98  
% 2.35/0.98  fof(f44,plain,(
% 2.35/0.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK0(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f30])).
% 2.35/0.98  
% 2.35/0.98  fof(f8,axiom,(
% 2.35/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f13,plain,(
% 2.35/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.35/0.98    inference(pure_predicate_removal,[],[f8])).
% 2.35/0.98  
% 2.35/0.98  fof(f23,plain,(
% 2.35/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.98    inference(ennf_transformation,[],[f13])).
% 2.35/0.98  
% 2.35/0.98  fof(f54,plain,(
% 2.35/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.35/0.98    inference(cnf_transformation,[],[f23])).
% 2.35/0.98  
% 2.35/0.98  fof(f2,axiom,(
% 2.35/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f15,plain,(
% 2.35/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.35/0.98    inference(ennf_transformation,[],[f2])).
% 2.35/0.98  
% 2.35/0.98  fof(f26,plain,(
% 2.35/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.35/0.98    inference(nnf_transformation,[],[f15])).
% 2.35/0.98  
% 2.35/0.98  fof(f41,plain,(
% 2.35/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f26])).
% 2.35/0.98  
% 2.35/0.98  fof(f6,axiom,(
% 2.35/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f20,plain,(
% 2.35/0.98    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.35/0.98    inference(ennf_transformation,[],[f6])).
% 2.35/0.98  
% 2.35/0.98  fof(f21,plain,(
% 2.35/0.98    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.35/0.98    inference(flattening,[],[f20])).
% 2.35/0.98  
% 2.35/0.98  fof(f52,plain,(
% 2.35/0.98    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f21])).
% 2.35/0.98  
% 2.35/0.98  fof(f5,axiom,(
% 2.35/0.98    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f19,plain,(
% 2.35/0.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))) | ~v1_relat_1(X3))),
% 2.35/0.98    inference(ennf_transformation,[],[f5])).
% 2.35/0.98  
% 2.35/0.98  fof(f31,plain,(
% 2.35/0.98    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | (~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))))) | ~v1_relat_1(X3))),
% 2.35/0.98    inference(nnf_transformation,[],[f19])).
% 2.35/0.98  
% 2.35/0.98  fof(f32,plain,(
% 2.35/0.98    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2)) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))))) | ~v1_relat_1(X3))),
% 2.35/0.98    inference(flattening,[],[f31])).
% 2.35/0.98  
% 2.35/0.98  fof(f49,plain,(
% 2.35/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X2) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | ~v1_relat_1(X3)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f32])).
% 2.35/0.98  
% 2.35/0.98  fof(f1,axiom,(
% 2.35/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f14,plain,(
% 2.35/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.35/0.98    inference(ennf_transformation,[],[f1])).
% 2.35/0.98  
% 2.35/0.98  fof(f40,plain,(
% 2.35/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f14])).
% 2.35/0.98  
% 2.35/0.98  fof(f45,plain,(
% 2.35/0.98    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f30])).
% 2.35/0.98  
% 2.35/0.98  fof(f61,plain,(
% 2.35/0.98    ( ! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(k4_tarski(sK5,X5),sK4) | ~m1_subset_1(X5,sK3) | ~r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2))) )),
% 2.35/0.98    inference(cnf_transformation,[],[f39])).
% 2.35/0.98  
% 2.35/0.98  fof(f60,plain,(
% 2.35/0.98    r2_hidden(sK6,sK2) | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2))),
% 2.35/0.98    inference(cnf_transformation,[],[f39])).
% 2.35/0.98  
% 2.35/0.98  cnf(c_21,negated_conjecture,
% 2.35/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 2.35/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1519,plain,
% 2.35/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_15,plain,
% 2.35/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.98      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.35/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1525,plain,
% 2.35/0.98      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.35/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1943,plain,
% 2.35/0.98      ( k8_relset_1(sK1,sK3,sK4,X0) = k10_relat_1(sK4,X0) ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_1519,c_1525]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_18,negated_conjecture,
% 2.35/0.98      ( r2_hidden(k4_tarski(sK5,sK6),sK4)
% 2.35/0.98      | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) ),
% 2.35/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1522,plain,
% 2.35/0.98      ( r2_hidden(k4_tarski(sK5,sK6),sK4) = iProver_top
% 2.35/0.98      | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) = iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2115,plain,
% 2.35/0.98      ( r2_hidden(k4_tarski(sK5,sK6),sK4) = iProver_top
% 2.35/0.98      | r2_hidden(sK5,k10_relat_1(sK4,sK2)) = iProver_top ),
% 2.35/0.98      inference(demodulation,[status(thm)],[c_1943,c_1522]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_3,plain,
% 2.35/0.98      ( ~ r2_hidden(X0,X1)
% 2.35/0.98      | r2_hidden(X2,k10_relat_1(X3,X1))
% 2.35/0.98      | ~ r2_hidden(X0,k2_relat_1(X3))
% 2.35/0.98      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 2.35/0.98      | ~ v1_relat_1(X3) ),
% 2.35/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1535,plain,
% 2.35/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.35/0.98      | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
% 2.35/0.98      | r2_hidden(X0,k2_relat_1(X3)) != iProver_top
% 2.35/0.98      | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
% 2.35/0.98      | v1_relat_1(X3) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7,plain,
% 2.35/0.98      ( r2_hidden(X0,k2_relat_1(X1))
% 2.35/0.98      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.35/0.98      | ~ v1_relat_1(X1) ),
% 2.35/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1531,plain,
% 2.35/0.98      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 2.35/0.98      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 2.35/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1632,plain,
% 2.35/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.35/0.98      | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
% 2.35/0.98      | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
% 2.35/0.98      | v1_relat_1(X3) != iProver_top ),
% 2.35/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_1535,c_1531]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_3302,plain,
% 2.35/0.98      ( r2_hidden(sK6,X0) != iProver_top
% 2.35/0.98      | r2_hidden(sK5,k10_relat_1(sK4,X0)) = iProver_top
% 2.35/0.98      | r2_hidden(sK5,k10_relat_1(sK4,sK2)) = iProver_top
% 2.35/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_2115,c_1632]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_22,plain,
% 2.35/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_13,plain,
% 2.35/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.35/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1682,plain,
% 2.35/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 2.35/0.98      | v1_relat_1(sK4) ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1683,plain,
% 2.35/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 2.35/0.98      | v1_relat_1(sK4) = iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1682]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_5,plain,
% 2.35/0.98      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 2.35/0.98      | r2_hidden(k4_tarski(X0,sK0(X0,X2,X1)),X1)
% 2.35/0.98      | ~ v1_relat_1(X1) ),
% 2.35/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1533,plain,
% 2.35/0.98      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 2.35/0.98      | r2_hidden(k4_tarski(X0,sK0(X0,X2,X1)),X1) = iProver_top
% 2.35/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_14,plain,
% 2.35/0.98      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.35/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2,plain,
% 2.35/0.98      ( r1_tarski(k2_relat_1(X0),X1) | ~ v5_relat_1(X0,X1) | ~ v1_relat_1(X0) ),
% 2.35/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_250,plain,
% 2.35/0.98      ( r1_tarski(k2_relat_1(X0),X1)
% 2.35/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.35/0.98      | ~ v1_relat_1(X0) ),
% 2.35/0.98      inference(resolution,[status(thm)],[c_14,c_2]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_260,plain,
% 2.35/0.98      ( r1_tarski(k2_relat_1(X0),X1)
% 2.35/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.35/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_250,c_13]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_12,plain,
% 2.35/0.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.35/0.98      | ~ v1_relat_1(X0)
% 2.35/0.98      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 2.35/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_270,plain,
% 2.35/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.98      | ~ v1_relat_1(X0)
% 2.35/0.98      | k5_relat_1(X0,k6_relat_1(X2)) = X0 ),
% 2.35/0.98      inference(resolution,[status(thm)],[c_260,c_12]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_274,plain,
% 2.35/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.98      | k5_relat_1(X0,k6_relat_1(X2)) = X0 ),
% 2.35/0.98      inference(global_propositional_subsumption,[status(thm)],[c_270,c_13]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1518,plain,
% 2.35/0.98      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 2.35/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_274]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1885,plain,
% 2.35/0.98      ( k5_relat_1(sK4,k6_relat_1(sK3)) = sK4 ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_1519,c_1518]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_11,plain,
% 2.35/0.98      ( r2_hidden(X0,X1)
% 2.35/0.98      | ~ r2_hidden(k4_tarski(X2,X0),k5_relat_1(X3,k6_relat_1(X1)))
% 2.35/0.98      | ~ v1_relat_1(X3) ),
% 2.35/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1527,plain,
% 2.35/0.98      ( r2_hidden(X0,X1) = iProver_top
% 2.35/0.98      | r2_hidden(k4_tarski(X2,X0),k5_relat_1(X3,k6_relat_1(X1))) != iProver_top
% 2.35/0.98      | v1_relat_1(X3) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2259,plain,
% 2.35/0.98      ( r2_hidden(X0,sK3) = iProver_top
% 2.35/0.98      | r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top
% 2.35/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_1885,c_1527]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2546,plain,
% 2.35/0.98      ( r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top
% 2.35/0.98      | r2_hidden(X0,sK3) = iProver_top ),
% 2.35/0.98      inference(global_propositional_subsumption,
% 2.35/0.98                [status(thm)],
% 2.35/0.98                [c_2259,c_22,c_1683]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2547,plain,
% 2.35/0.98      ( r2_hidden(X0,sK3) = iProver_top
% 2.35/0.98      | r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top ),
% 2.35/0.98      inference(renaming,[status(thm)],[c_2546]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2921,plain,
% 2.35/0.98      ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
% 2.35/0.98      | r2_hidden(sK0(X0,X1,sK4),sK3) = iProver_top
% 2.35/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_1533,c_2547]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_3248,plain,
% 2.35/0.98      ( r2_hidden(sK0(X0,X1,sK4),sK3) = iProver_top
% 2.35/0.98      | r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top ),
% 2.35/0.98      inference(global_propositional_subsumption,
% 2.35/0.98                [status(thm)],
% 2.35/0.98                [c_2921,c_22,c_1683]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_3249,plain,
% 2.35/0.98      ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
% 2.35/0.98      | r2_hidden(sK0(X0,X1,sK4),sK3) = iProver_top ),
% 2.35/0.98      inference(renaming,[status(thm)],[c_3248]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_0,plain,
% 2.35/0.98      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 2.35/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1536,plain,
% 2.35/0.98      ( r2_hidden(X0,X1) != iProver_top | m1_subset_1(X0,X1) = iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_3256,plain,
% 2.35/0.98      ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
% 2.35/0.98      | m1_subset_1(sK0(X0,X1,sK4),sK3) = iProver_top ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_3249,c_1536]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_4,plain,
% 2.35/0.98      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 2.35/0.98      | r2_hidden(sK0(X0,X2,X1),X2)
% 2.35/0.98      | ~ v1_relat_1(X1) ),
% 2.35/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1534,plain,
% 2.35/0.98      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 2.35/0.98      | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
% 2.35/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_16,negated_conjecture,
% 2.35/0.98      ( ~ r2_hidden(X0,sK2)
% 2.35/0.98      | ~ r2_hidden(k4_tarski(sK5,X0),sK4)
% 2.35/0.98      | ~ r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2))
% 2.35/0.98      | ~ m1_subset_1(X0,sK3) ),
% 2.35/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1524,plain,
% 2.35/0.98      ( r2_hidden(X0,sK2) != iProver_top
% 2.35/0.98      | r2_hidden(k4_tarski(sK5,X0),sK4) != iProver_top
% 2.35/0.98      | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) != iProver_top
% 2.35/0.98      | m1_subset_1(X0,sK3) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2118,plain,
% 2.35/0.98      ( r2_hidden(X0,sK2) != iProver_top
% 2.35/0.98      | r2_hidden(k4_tarski(sK5,X0),sK4) != iProver_top
% 2.35/0.98      | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
% 2.35/0.98      | m1_subset_1(X0,sK3) != iProver_top ),
% 2.35/0.98      inference(demodulation,[status(thm)],[c_1943,c_1524]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2917,plain,
% 2.35/0.98      ( r2_hidden(sK0(sK5,X0,sK4),sK2) != iProver_top
% 2.35/0.98      | r2_hidden(sK5,k10_relat_1(sK4,X0)) != iProver_top
% 2.35/0.98      | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
% 2.35/0.98      | m1_subset_1(sK0(sK5,X0,sK4),sK3) != iProver_top
% 2.35/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_1533,c_2118]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_3187,plain,
% 2.35/0.98      ( m1_subset_1(sK0(sK5,X0,sK4),sK3) != iProver_top
% 2.35/0.98      | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
% 2.35/0.98      | r2_hidden(sK5,k10_relat_1(sK4,X0)) != iProver_top
% 2.35/0.98      | r2_hidden(sK0(sK5,X0,sK4),sK2) != iProver_top ),
% 2.35/0.98      inference(global_propositional_subsumption,
% 2.35/0.98                [status(thm)],
% 2.35/0.98                [c_2917,c_22,c_1683]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_3188,plain,
% 2.35/0.98      ( r2_hidden(sK0(sK5,X0,sK4),sK2) != iProver_top
% 2.35/0.98      | r2_hidden(sK5,k10_relat_1(sK4,X0)) != iProver_top
% 2.35/0.98      | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
% 2.35/0.98      | m1_subset_1(sK0(sK5,X0,sK4),sK3) != iProver_top ),
% 2.35/0.98      inference(renaming,[status(thm)],[c_3187]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_3197,plain,
% 2.35/0.98      ( r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
% 2.35/0.98      | m1_subset_1(sK0(sK5,sK2,sK4),sK3) != iProver_top
% 2.35/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_1534,c_3188]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_3283,plain,
% 2.35/0.98      ( m1_subset_1(sK0(sK5,sK2,sK4),sK3) != iProver_top
% 2.35/0.98      | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top ),
% 2.35/0.98      inference(global_propositional_subsumption,
% 2.35/0.98                [status(thm)],
% 2.35/0.98                [c_3197,c_22,c_1683]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_3284,plain,
% 2.35/0.98      ( r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
% 2.35/0.98      | m1_subset_1(sK0(sK5,sK2,sK4),sK3) != iProver_top ),
% 2.35/0.98      inference(renaming,[status(thm)],[c_3283]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_3412,plain,
% 2.35/0.98      ( r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_3256,c_3284]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_3415,plain,
% 2.35/0.98      ( r2_hidden(sK6,X0) != iProver_top
% 2.35/0.98      | r2_hidden(sK5,k10_relat_1(sK4,X0)) = iProver_top ),
% 2.35/0.98      inference(global_propositional_subsumption,
% 2.35/0.98                [status(thm)],
% 2.35/0.98                [c_3302,c_22,c_1683,c_3412]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_4048,plain,
% 2.35/0.98      ( r2_hidden(sK6,sK2) != iProver_top ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_3415,c_3412]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_17,negated_conjecture,
% 2.35/0.98      ( r2_hidden(sK6,sK2) | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) ),
% 2.35/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1523,plain,
% 2.35/0.98      ( r2_hidden(sK6,sK2) = iProver_top
% 2.35/0.98      | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) = iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2116,plain,
% 2.35/0.98      ( r2_hidden(sK6,sK2) = iProver_top
% 2.35/0.98      | r2_hidden(sK5,k10_relat_1(sK4,sK2)) = iProver_top ),
% 2.35/0.98      inference(demodulation,[status(thm)],[c_1943,c_1523]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_4053,plain,
% 2.35/0.98      ( r2_hidden(sK6,sK2) = iProver_top ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_2116,c_3412]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_4061,plain,
% 2.35/0.98      ( $false ),
% 2.35/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_4048,c_4053]) ).
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.35/0.98  
% 2.35/0.98  ------                               Statistics
% 2.35/0.98  
% 2.35/0.98  ------ General
% 2.35/0.98  
% 2.35/0.98  abstr_ref_over_cycles:                  0
% 2.35/0.98  abstr_ref_under_cycles:                 0
% 2.35/0.98  gc_basic_clause_elim:                   0
% 2.35/0.98  forced_gc_time:                         0
% 2.35/0.98  parsing_time:                           0.009
% 2.35/0.98  unif_index_cands_time:                  0.
% 2.35/0.98  unif_index_add_time:                    0.
% 2.35/0.98  orderings_time:                         0.
% 2.35/0.98  out_proof_time:                         0.007
% 2.35/0.98  total_time:                             0.137
% 2.35/0.98  num_of_symbols:                         52
% 2.35/0.98  num_of_terms:                           2937
% 2.35/0.98  
% 2.35/0.98  ------ Preprocessing
% 2.35/0.98  
% 2.35/0.98  num_of_splits:                          0
% 2.35/0.98  num_of_split_atoms:                     0
% 2.35/0.98  num_of_reused_defs:                     0
% 2.35/0.98  num_eq_ax_congr_red:                    33
% 2.35/0.98  num_of_sem_filtered_clauses:            1
% 2.35/0.98  num_of_subtypes:                        0
% 2.35/0.98  monotx_restored_types:                  0
% 2.35/0.98  sat_num_of_epr_types:                   0
% 2.35/0.98  sat_num_of_non_cyclic_types:            0
% 2.35/0.98  sat_guarded_non_collapsed_types:        0
% 2.35/0.98  num_pure_diseq_elim:                    0
% 2.35/0.98  simp_replaced_by:                       0
% 2.35/0.98  res_preprocessed:                       98
% 2.35/0.98  prep_upred:                             0
% 2.35/0.98  prep_unflattend:                        58
% 2.35/0.98  smt_new_axioms:                         0
% 2.35/0.98  pred_elim_cands:                        3
% 2.35/0.98  pred_elim:                              2
% 2.35/0.98  pred_elim_cl:                           3
% 2.35/0.98  pred_elim_cycles:                       6
% 2.35/0.98  merged_defs:                            0
% 2.35/0.98  merged_defs_ncl:                        0
% 2.35/0.98  bin_hyper_res:                          0
% 2.35/0.98  prep_cycles:                            4
% 2.35/0.98  pred_elim_time:                         0.012
% 2.35/0.98  splitting_time:                         0.
% 2.35/0.98  sem_filter_time:                        0.
% 2.35/0.98  monotx_time:                            0.
% 2.35/0.98  subtype_inf_time:                       0.
% 2.35/0.98  
% 2.35/0.98  ------ Problem properties
% 2.35/0.98  
% 2.35/0.98  clauses:                                19
% 2.35/0.98  conjectures:                            6
% 2.35/0.98  epr:                                    2
% 2.35/0.98  horn:                                   16
% 2.35/0.98  ground:                                 5
% 2.35/0.98  unary:                                  2
% 2.35/0.98  binary:                                 7
% 2.35/0.98  lits:                                   50
% 2.35/0.98  lits_eq:                                2
% 2.35/0.98  fd_pure:                                0
% 2.35/0.98  fd_pseudo:                              0
% 2.35/0.98  fd_cond:                                0
% 2.35/0.98  fd_pseudo_cond:                         0
% 2.35/0.98  ac_symbols:                             0
% 2.35/0.98  
% 2.35/0.98  ------ Propositional Solver
% 2.35/0.98  
% 2.35/0.98  prop_solver_calls:                      29
% 2.35/0.98  prop_fast_solver_calls:                 885
% 2.35/0.98  smt_solver_calls:                       0
% 2.35/0.98  smt_fast_solver_calls:                  0
% 2.35/0.98  prop_num_of_clauses:                    1320
% 2.35/0.98  prop_preprocess_simplified:             4250
% 2.35/0.98  prop_fo_subsumed:                       21
% 2.35/0.98  prop_solver_time:                       0.
% 2.35/0.98  smt_solver_time:                        0.
% 2.35/0.98  smt_fast_solver_time:                   0.
% 2.35/0.98  prop_fast_solver_time:                  0.
% 2.35/0.98  prop_unsat_core_time:                   0.
% 2.35/0.98  
% 2.35/0.98  ------ QBF
% 2.35/0.98  
% 2.35/0.98  qbf_q_res:                              0
% 2.35/0.98  qbf_num_tautologies:                    0
% 2.35/0.98  qbf_prep_cycles:                        0
% 2.35/0.98  
% 2.35/0.98  ------ BMC1
% 2.35/0.98  
% 2.35/0.98  bmc1_current_bound:                     -1
% 2.35/0.98  bmc1_last_solved_bound:                 -1
% 2.35/0.98  bmc1_unsat_core_size:                   -1
% 2.35/0.98  bmc1_unsat_core_parents_size:           -1
% 2.35/0.98  bmc1_merge_next_fun:                    0
% 2.35/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.35/0.98  
% 2.35/0.98  ------ Instantiation
% 2.35/0.98  
% 2.35/0.98  inst_num_of_clauses:                    358
% 2.35/0.98  inst_num_in_passive:                    51
% 2.35/0.98  inst_num_in_active:                     249
% 2.35/0.98  inst_num_in_unprocessed:                58
% 2.35/0.98  inst_num_of_loops:                      300
% 2.35/0.98  inst_num_of_learning_restarts:          0
% 2.35/0.98  inst_num_moves_active_passive:          46
% 2.35/0.98  inst_lit_activity:                      0
% 2.35/0.98  inst_lit_activity_moves:                0
% 2.35/0.98  inst_num_tautologies:                   0
% 2.35/0.98  inst_num_prop_implied:                  0
% 2.35/0.98  inst_num_existing_simplified:           0
% 2.35/0.98  inst_num_eq_res_simplified:             0
% 2.35/0.98  inst_num_child_elim:                    0
% 2.35/0.98  inst_num_of_dismatching_blockings:      26
% 2.35/0.98  inst_num_of_non_proper_insts:           309
% 2.35/0.98  inst_num_of_duplicates:                 0
% 2.35/0.98  inst_inst_num_from_inst_to_res:         0
% 2.35/0.98  inst_dismatching_checking_time:         0.
% 2.35/0.98  
% 2.35/0.98  ------ Resolution
% 2.35/0.98  
% 2.35/0.98  res_num_of_clauses:                     0
% 2.35/0.98  res_num_in_passive:                     0
% 2.35/0.98  res_num_in_active:                      0
% 2.35/0.98  res_num_of_loops:                       102
% 2.35/0.98  res_forward_subset_subsumed:            55
% 2.35/0.98  res_backward_subset_subsumed:           2
% 2.35/0.98  res_forward_subsumed:                   0
% 2.35/0.98  res_backward_subsumed:                  0
% 2.35/0.98  res_forward_subsumption_resolution:     2
% 2.35/0.98  res_backward_subsumption_resolution:    0
% 2.35/0.98  res_clause_to_clause_subsumption:       183
% 2.35/0.98  res_orphan_elimination:                 0
% 2.35/0.98  res_tautology_del:                      64
% 2.35/0.98  res_num_eq_res_simplified:              0
% 2.35/0.98  res_num_sel_changes:                    0
% 2.35/0.98  res_moves_from_active_to_pass:          0
% 2.35/0.98  
% 2.35/0.98  ------ Superposition
% 2.35/0.98  
% 2.35/0.98  sup_time_total:                         0.
% 2.35/0.98  sup_time_generating:                    0.
% 2.35/0.98  sup_time_sim_full:                      0.
% 2.35/0.98  sup_time_sim_immed:                     0.
% 2.35/0.98  
% 2.35/0.98  sup_num_of_clauses:                     70
% 2.35/0.98  sup_num_in_active:                      52
% 2.35/0.98  sup_num_in_passive:                     18
% 2.35/0.98  sup_num_of_loops:                       59
% 2.35/0.98  sup_fw_superposition:                   36
% 2.35/0.98  sup_bw_superposition:                   51
% 2.35/0.98  sup_immediate_simplified:               8
% 2.35/0.98  sup_given_eliminated:                   0
% 2.35/0.98  comparisons_done:                       0
% 2.35/0.98  comparisons_avoided:                    0
% 2.35/0.98  
% 2.35/0.98  ------ Simplifications
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  sim_fw_subset_subsumed:                 2
% 2.35/0.98  sim_bw_subset_subsumed:                 9
% 2.35/0.98  sim_fw_subsumed:                        3
% 2.35/0.98  sim_bw_subsumed:                        3
% 2.35/0.98  sim_fw_subsumption_res:                 2
% 2.35/0.98  sim_bw_subsumption_res:                 0
% 2.35/0.98  sim_tautology_del:                      9
% 2.35/0.98  sim_eq_tautology_del:                   0
% 2.35/0.98  sim_eq_res_simp:                        0
% 2.35/0.98  sim_fw_demodulated:                     3
% 2.35/0.98  sim_bw_demodulated:                     4
% 2.35/0.98  sim_light_normalised:                   0
% 2.35/0.98  sim_joinable_taut:                      0
% 2.35/0.98  sim_joinable_simp:                      0
% 2.35/0.98  sim_ac_normalised:                      0
% 2.35/0.98  sim_smt_subsumption:                    0
% 2.35/0.98  
%------------------------------------------------------------------------------

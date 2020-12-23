%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:03 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 591 expanded)
%              Number of clauses        :   58 ( 161 expanded)
%              Number of leaves         :   13 ( 148 expanded)
%              Depth                    :   20
%              Number of atoms          :  421 (3939 expanded)
%              Number of equality atoms :  134 ( 329 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f22,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK1(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22,f21,f20])).

fof(f37,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f36,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X4,X2,X3,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X4,X6),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK8,X1)
        & r2_hidden(k4_tarski(X4,sK8),X3)
        & m1_subset_1(sK8,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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

fof(f27,plain,
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
                ( ~ r2_hidden(X5,sK4)
                | ~ r2_hidden(k4_tarski(X4,X5),sK6)
                | ~ m1_subset_1(X5,sK5) )
            | ~ r2_hidden(X4,k8_relset_1(sK3,sK5,sK6,sK4)) )
          & ( ? [X6] :
                ( r2_hidden(X6,sK4)
                & r2_hidden(k4_tarski(X4,X6),sK6)
                & m1_subset_1(X6,sK5) )
            | r2_hidden(X4,k8_relset_1(sK3,sK5,sK6,sK4)) )
          & m1_subset_1(X4,sK3) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
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
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f26,f29,f28,f27])).

fof(f44,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f16])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,
    ( m1_subset_1(sK8,sK5)
    | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK4)
      | ~ r2_hidden(k4_tarski(sK7,X5),sK6)
      | ~ m1_subset_1(X5,sK5)
      | ~ r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),sK6)
    | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) ),
    inference(cnf_transformation,[],[f30])).

fof(f38,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f48,plain,
    ( r2_hidden(sK8,sK4)
    | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_924,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK2(X1,X2,X0),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK2(X1,X2,X0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_923,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(X1,X2,X0)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_915,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_930,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2033,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK3,sK5)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_915,c_930])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_932,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2245,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2033,c_932])).

cnf(c_2580,plain,
    ( r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_923,c_2245])).

cnf(c_19,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1079,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1080,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1079])).

cnf(c_3729,plain,
    ( r2_hidden(sK2(sK6,X1,X0),sK5) = iProver_top
    | r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2580,c_19,c_1080])).

cnf(c_3730,plain,
    ( r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_3729])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_929,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3737,plain,
    ( m1_subset_1(sK2(sK6,X0,X1),sK5) = iProver_top
    | r2_hidden(X1,k10_relat_1(sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3730,c_929])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK8,sK5)
    | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_917,plain,
    ( m1_subset_1(sK8,sK5) = iProver_top
    | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(k4_tarski(sK7,X0),sK6)
    | ~ r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_920,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top
    | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1119,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | m1_subset_1(sK8,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_917,c_920])).

cnf(c_1837,plain,
    ( m1_subset_1(sK2(sK6,X0,sK7),sK5) != iProver_top
    | m1_subset_1(sK8,sK5) = iProver_top
    | r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_923,c_1119])).

cnf(c_2969,plain,
    ( r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top
    | r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
    | m1_subset_1(sK8,sK5) = iProver_top
    | m1_subset_1(sK2(sK6,X0,sK7),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1837,c_19,c_1080])).

cnf(c_2970,plain,
    ( m1_subset_1(sK2(sK6,X0,sK7),sK5) != iProver_top
    | m1_subset_1(sK8,sK5) = iProver_top
    | r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2969])).

cnf(c_4232,plain,
    ( m1_subset_1(sK8,sK5) = iProver_top
    | r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3737,c_2970])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_921,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1508,plain,
    ( k8_relset_1(sK3,sK5,sK6,X0) = k10_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_915,c_921])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(k4_tarski(sK7,sK8),sK6)
    | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_918,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),sK6) = iProver_top
    | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1672,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),sK6) = iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1508,c_918])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_925,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2247,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(k2_zfmisc_1(sK3,sK5),X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK6) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2033,c_925])).

cnf(c_2656,plain,
    ( r2_hidden(sK8,X0) != iProver_top
    | r2_hidden(sK7,k10_relat_1(k2_zfmisc_1(sK3,sK5),X0)) = iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1672,c_2247])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK8,sK4)
    | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_919,plain,
    ( r2_hidden(sK8,sK4) = iProver_top
    | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1673,plain,
    ( r2_hidden(sK8,sK4) = iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1508,c_919])).

cnf(c_2284,plain,
    ( r2_hidden(sK8,X0) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,X0)) = iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1672,c_925])).

cnf(c_3207,plain,
    ( r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,X0)) = iProver_top
    | r2_hidden(sK8,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2284,c_19,c_1080])).

cnf(c_3208,plain,
    ( r2_hidden(sK8,X0) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,X0)) = iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3207])).

cnf(c_3218,plain,
    ( r2_hidden(sK8,sK4) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3208])).

cnf(c_3220,plain,
    ( r2_hidden(sK8,sK4) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3218])).

cnf(c_3672,plain,
    ( r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2656,c_1673,c_3220])).

cnf(c_1675,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1508,c_920])).

cnf(c_1834,plain,
    ( m1_subset_1(sK2(sK6,X0,sK7),sK5) != iProver_top
    | r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,sK4)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_923,c_1675])).

cnf(c_3011,plain,
    ( r2_hidden(sK7,k10_relat_1(sK6,sK4)) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top
    | r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
    | m1_subset_1(sK2(sK6,X0,sK7),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1834,c_19,c_1080])).

cnf(c_3012,plain,
    ( m1_subset_1(sK2(sK6,X0,sK7),sK5) != iProver_top
    | r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3011])).

cnf(c_4230,plain,
    ( r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3737,c_3012])).

cnf(c_5151,plain,
    ( r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
    | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4232,c_1673,c_3220,c_4230])).

cnf(c_5159,plain,
    ( r2_hidden(sK7,k10_relat_1(sK6,sK4)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_924,c_5151])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5159,c_3672,c_1080,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.59/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.01  
% 2.59/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.59/1.01  
% 2.59/1.01  ------  iProver source info
% 2.59/1.01  
% 2.59/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.59/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.59/1.01  git: non_committed_changes: false
% 2.59/1.01  git: last_make_outside_of_git: false
% 2.59/1.01  
% 2.59/1.01  ------ 
% 2.59/1.01  
% 2.59/1.01  ------ Input Options
% 2.59/1.01  
% 2.59/1.01  --out_options                           all
% 2.59/1.01  --tptp_safe_out                         true
% 2.59/1.01  --problem_path                          ""
% 2.59/1.01  --include_path                          ""
% 2.59/1.01  --clausifier                            res/vclausify_rel
% 2.59/1.01  --clausifier_options                    --mode clausify
% 2.59/1.01  --stdin                                 false
% 2.59/1.01  --stats_out                             all
% 2.59/1.01  
% 2.59/1.01  ------ General Options
% 2.59/1.01  
% 2.59/1.01  --fof                                   false
% 2.59/1.01  --time_out_real                         305.
% 2.59/1.01  --time_out_virtual                      -1.
% 2.59/1.01  --symbol_type_check                     false
% 2.59/1.01  --clausify_out                          false
% 2.59/1.01  --sig_cnt_out                           false
% 2.59/1.01  --trig_cnt_out                          false
% 2.59/1.01  --trig_cnt_out_tolerance                1.
% 2.59/1.01  --trig_cnt_out_sk_spl                   false
% 2.59/1.01  --abstr_cl_out                          false
% 2.59/1.01  
% 2.59/1.01  ------ Global Options
% 2.59/1.01  
% 2.59/1.01  --schedule                              default
% 2.59/1.01  --add_important_lit                     false
% 2.59/1.01  --prop_solver_per_cl                    1000
% 2.59/1.01  --min_unsat_core                        false
% 2.59/1.01  --soft_assumptions                      false
% 2.59/1.01  --soft_lemma_size                       3
% 2.59/1.01  --prop_impl_unit_size                   0
% 2.59/1.01  --prop_impl_unit                        []
% 2.59/1.01  --share_sel_clauses                     true
% 2.59/1.01  --reset_solvers                         false
% 2.59/1.01  --bc_imp_inh                            [conj_cone]
% 2.59/1.01  --conj_cone_tolerance                   3.
% 2.59/1.01  --extra_neg_conj                        none
% 2.59/1.01  --large_theory_mode                     true
% 2.59/1.01  --prolific_symb_bound                   200
% 2.59/1.01  --lt_threshold                          2000
% 2.59/1.01  --clause_weak_htbl                      true
% 2.59/1.01  --gc_record_bc_elim                     false
% 2.59/1.01  
% 2.59/1.01  ------ Preprocessing Options
% 2.59/1.01  
% 2.59/1.01  --preprocessing_flag                    true
% 2.59/1.01  --time_out_prep_mult                    0.1
% 2.59/1.01  --splitting_mode                        input
% 2.59/1.01  --splitting_grd                         true
% 2.59/1.01  --splitting_cvd                         false
% 2.59/1.01  --splitting_cvd_svl                     false
% 2.59/1.01  --splitting_nvd                         32
% 2.59/1.01  --sub_typing                            true
% 2.59/1.01  --prep_gs_sim                           true
% 2.59/1.01  --prep_unflatten                        true
% 2.59/1.01  --prep_res_sim                          true
% 2.59/1.01  --prep_upred                            true
% 2.59/1.01  --prep_sem_filter                       exhaustive
% 2.59/1.01  --prep_sem_filter_out                   false
% 2.59/1.01  --pred_elim                             true
% 2.59/1.01  --res_sim_input                         true
% 2.59/1.01  --eq_ax_congr_red                       true
% 2.59/1.01  --pure_diseq_elim                       true
% 2.59/1.01  --brand_transform                       false
% 2.59/1.01  --non_eq_to_eq                          false
% 2.59/1.01  --prep_def_merge                        true
% 2.59/1.01  --prep_def_merge_prop_impl              false
% 2.59/1.01  --prep_def_merge_mbd                    true
% 2.59/1.01  --prep_def_merge_tr_red                 false
% 2.59/1.01  --prep_def_merge_tr_cl                  false
% 2.59/1.01  --smt_preprocessing                     true
% 2.59/1.01  --smt_ac_axioms                         fast
% 2.59/1.01  --preprocessed_out                      false
% 2.59/1.01  --preprocessed_stats                    false
% 2.59/1.01  
% 2.59/1.01  ------ Abstraction refinement Options
% 2.59/1.01  
% 2.59/1.01  --abstr_ref                             []
% 2.59/1.01  --abstr_ref_prep                        false
% 2.59/1.01  --abstr_ref_until_sat                   false
% 2.59/1.01  --abstr_ref_sig_restrict                funpre
% 2.59/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/1.01  --abstr_ref_under                       []
% 2.59/1.01  
% 2.59/1.01  ------ SAT Options
% 2.59/1.01  
% 2.59/1.01  --sat_mode                              false
% 2.59/1.01  --sat_fm_restart_options                ""
% 2.59/1.01  --sat_gr_def                            false
% 2.59/1.01  --sat_epr_types                         true
% 2.59/1.01  --sat_non_cyclic_types                  false
% 2.59/1.01  --sat_finite_models                     false
% 2.59/1.01  --sat_fm_lemmas                         false
% 2.59/1.01  --sat_fm_prep                           false
% 2.59/1.01  --sat_fm_uc_incr                        true
% 2.59/1.01  --sat_out_model                         small
% 2.59/1.01  --sat_out_clauses                       false
% 2.59/1.01  
% 2.59/1.01  ------ QBF Options
% 2.59/1.01  
% 2.59/1.01  --qbf_mode                              false
% 2.59/1.01  --qbf_elim_univ                         false
% 2.59/1.01  --qbf_dom_inst                          none
% 2.59/1.01  --qbf_dom_pre_inst                      false
% 2.59/1.01  --qbf_sk_in                             false
% 2.59/1.01  --qbf_pred_elim                         true
% 2.59/1.01  --qbf_split                             512
% 2.59/1.01  
% 2.59/1.01  ------ BMC1 Options
% 2.59/1.01  
% 2.59/1.01  --bmc1_incremental                      false
% 2.59/1.01  --bmc1_axioms                           reachable_all
% 2.59/1.01  --bmc1_min_bound                        0
% 2.59/1.01  --bmc1_max_bound                        -1
% 2.59/1.01  --bmc1_max_bound_default                -1
% 2.59/1.01  --bmc1_symbol_reachability              true
% 2.59/1.01  --bmc1_property_lemmas                  false
% 2.59/1.01  --bmc1_k_induction                      false
% 2.59/1.01  --bmc1_non_equiv_states                 false
% 2.59/1.01  --bmc1_deadlock                         false
% 2.59/1.01  --bmc1_ucm                              false
% 2.59/1.01  --bmc1_add_unsat_core                   none
% 2.59/1.01  --bmc1_unsat_core_children              false
% 2.59/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/1.01  --bmc1_out_stat                         full
% 2.59/1.01  --bmc1_ground_init                      false
% 2.59/1.01  --bmc1_pre_inst_next_state              false
% 2.59/1.01  --bmc1_pre_inst_state                   false
% 2.59/1.01  --bmc1_pre_inst_reach_state             false
% 2.59/1.01  --bmc1_out_unsat_core                   false
% 2.59/1.01  --bmc1_aig_witness_out                  false
% 2.59/1.01  --bmc1_verbose                          false
% 2.59/1.01  --bmc1_dump_clauses_tptp                false
% 2.59/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.59/1.01  --bmc1_dump_file                        -
% 2.59/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.59/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.59/1.01  --bmc1_ucm_extend_mode                  1
% 2.59/1.01  --bmc1_ucm_init_mode                    2
% 2.59/1.01  --bmc1_ucm_cone_mode                    none
% 2.59/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.59/1.01  --bmc1_ucm_relax_model                  4
% 2.59/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.59/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/1.01  --bmc1_ucm_layered_model                none
% 2.59/1.01  --bmc1_ucm_max_lemma_size               10
% 2.59/1.01  
% 2.59/1.01  ------ AIG Options
% 2.59/1.01  
% 2.59/1.01  --aig_mode                              false
% 2.59/1.01  
% 2.59/1.01  ------ Instantiation Options
% 2.59/1.01  
% 2.59/1.01  --instantiation_flag                    true
% 2.59/1.01  --inst_sos_flag                         false
% 2.59/1.01  --inst_sos_phase                        true
% 2.59/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/1.01  --inst_lit_sel_side                     num_symb
% 2.59/1.01  --inst_solver_per_active                1400
% 2.59/1.01  --inst_solver_calls_frac                1.
% 2.59/1.01  --inst_passive_queue_type               priority_queues
% 2.59/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/1.01  --inst_passive_queues_freq              [25;2]
% 2.59/1.01  --inst_dismatching                      true
% 2.59/1.01  --inst_eager_unprocessed_to_passive     true
% 2.59/1.01  --inst_prop_sim_given                   true
% 2.59/1.01  --inst_prop_sim_new                     false
% 2.59/1.01  --inst_subs_new                         false
% 2.59/1.01  --inst_eq_res_simp                      false
% 2.59/1.01  --inst_subs_given                       false
% 2.59/1.01  --inst_orphan_elimination               true
% 2.59/1.01  --inst_learning_loop_flag               true
% 2.59/1.01  --inst_learning_start                   3000
% 2.59/1.01  --inst_learning_factor                  2
% 2.59/1.01  --inst_start_prop_sim_after_learn       3
% 2.59/1.01  --inst_sel_renew                        solver
% 2.59/1.01  --inst_lit_activity_flag                true
% 2.59/1.01  --inst_restr_to_given                   false
% 2.59/1.01  --inst_activity_threshold               500
% 2.59/1.01  --inst_out_proof                        true
% 2.59/1.01  
% 2.59/1.01  ------ Resolution Options
% 2.59/1.01  
% 2.59/1.01  --resolution_flag                       true
% 2.59/1.01  --res_lit_sel                           adaptive
% 2.59/1.01  --res_lit_sel_side                      none
% 2.59/1.01  --res_ordering                          kbo
% 2.59/1.01  --res_to_prop_solver                    active
% 2.59/1.01  --res_prop_simpl_new                    false
% 2.59/1.01  --res_prop_simpl_given                  true
% 2.59/1.01  --res_passive_queue_type                priority_queues
% 2.59/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/1.01  --res_passive_queues_freq               [15;5]
% 2.59/1.01  --res_forward_subs                      full
% 2.59/1.01  --res_backward_subs                     full
% 2.59/1.01  --res_forward_subs_resolution           true
% 2.59/1.01  --res_backward_subs_resolution          true
% 2.59/1.01  --res_orphan_elimination                true
% 2.59/1.01  --res_time_limit                        2.
% 2.59/1.01  --res_out_proof                         true
% 2.59/1.01  
% 2.59/1.01  ------ Superposition Options
% 2.59/1.01  
% 2.59/1.01  --superposition_flag                    true
% 2.59/1.01  --sup_passive_queue_type                priority_queues
% 2.59/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.59/1.01  --demod_completeness_check              fast
% 2.59/1.01  --demod_use_ground                      true
% 2.59/1.01  --sup_to_prop_solver                    passive
% 2.59/1.01  --sup_prop_simpl_new                    true
% 2.59/1.01  --sup_prop_simpl_given                  true
% 2.59/1.01  --sup_fun_splitting                     false
% 2.59/1.01  --sup_smt_interval                      50000
% 2.59/1.01  
% 2.59/1.01  ------ Superposition Simplification Setup
% 2.59/1.01  
% 2.59/1.01  --sup_indices_passive                   []
% 2.59/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/1.01  --sup_full_bw                           [BwDemod]
% 2.59/1.01  --sup_immed_triv                        [TrivRules]
% 2.59/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/1.01  --sup_immed_bw_main                     []
% 2.59/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/1.01  
% 2.59/1.01  ------ Combination Options
% 2.59/1.01  
% 2.59/1.01  --comb_res_mult                         3
% 2.59/1.01  --comb_sup_mult                         2
% 2.59/1.01  --comb_inst_mult                        10
% 2.59/1.01  
% 2.59/1.01  ------ Debug Options
% 2.59/1.01  
% 2.59/1.01  --dbg_backtrace                         false
% 2.59/1.01  --dbg_dump_prop_clauses                 false
% 2.59/1.01  --dbg_dump_prop_clauses_file            -
% 2.59/1.01  --dbg_out_stat                          false
% 2.59/1.01  ------ Parsing...
% 2.59/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.59/1.01  
% 2.59/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.59/1.01  
% 2.59/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.59/1.01  
% 2.59/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.59/1.01  ------ Proving...
% 2.59/1.01  ------ Problem Properties 
% 2.59/1.01  
% 2.59/1.01  
% 2.59/1.01  clauses                                 19
% 2.59/1.01  conjectures                             6
% 2.59/1.01  EPR                                     2
% 2.59/1.01  Horn                                    14
% 2.59/1.01  unary                                   2
% 2.59/1.01  binary                                  8
% 2.59/1.01  lits                                    51
% 2.59/1.01  lits eq                                 4
% 2.59/1.01  fd_pure                                 0
% 2.59/1.01  fd_pseudo                               0
% 2.59/1.01  fd_cond                                 0
% 2.59/1.01  fd_pseudo_cond                          3
% 2.59/1.01  AC symbols                              0
% 2.59/1.01  
% 2.59/1.01  ------ Schedule dynamic 5 is on 
% 2.59/1.01  
% 2.59/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.59/1.01  
% 2.59/1.01  
% 2.59/1.01  ------ 
% 2.59/1.01  Current options:
% 2.59/1.01  ------ 
% 2.59/1.01  
% 2.59/1.01  ------ Input Options
% 2.59/1.01  
% 2.59/1.01  --out_options                           all
% 2.59/1.01  --tptp_safe_out                         true
% 2.59/1.01  --problem_path                          ""
% 2.59/1.01  --include_path                          ""
% 2.59/1.01  --clausifier                            res/vclausify_rel
% 2.59/1.01  --clausifier_options                    --mode clausify
% 2.59/1.01  --stdin                                 false
% 2.59/1.01  --stats_out                             all
% 2.59/1.01  
% 2.59/1.01  ------ General Options
% 2.59/1.01  
% 2.59/1.01  --fof                                   false
% 2.59/1.01  --time_out_real                         305.
% 2.59/1.01  --time_out_virtual                      -1.
% 2.59/1.01  --symbol_type_check                     false
% 2.59/1.01  --clausify_out                          false
% 2.59/1.01  --sig_cnt_out                           false
% 2.59/1.01  --trig_cnt_out                          false
% 2.59/1.01  --trig_cnt_out_tolerance                1.
% 2.59/1.01  --trig_cnt_out_sk_spl                   false
% 2.59/1.01  --abstr_cl_out                          false
% 2.59/1.01  
% 2.59/1.01  ------ Global Options
% 2.59/1.01  
% 2.59/1.01  --schedule                              default
% 2.59/1.01  --add_important_lit                     false
% 2.59/1.01  --prop_solver_per_cl                    1000
% 2.59/1.01  --min_unsat_core                        false
% 2.59/1.01  --soft_assumptions                      false
% 2.59/1.01  --soft_lemma_size                       3
% 2.59/1.01  --prop_impl_unit_size                   0
% 2.59/1.01  --prop_impl_unit                        []
% 2.59/1.01  --share_sel_clauses                     true
% 2.59/1.01  --reset_solvers                         false
% 2.59/1.01  --bc_imp_inh                            [conj_cone]
% 2.59/1.01  --conj_cone_tolerance                   3.
% 2.59/1.01  --extra_neg_conj                        none
% 2.59/1.01  --large_theory_mode                     true
% 2.59/1.01  --prolific_symb_bound                   200
% 2.59/1.01  --lt_threshold                          2000
% 2.59/1.01  --clause_weak_htbl                      true
% 2.59/1.01  --gc_record_bc_elim                     false
% 2.59/1.01  
% 2.59/1.01  ------ Preprocessing Options
% 2.59/1.01  
% 2.59/1.01  --preprocessing_flag                    true
% 2.59/1.01  --time_out_prep_mult                    0.1
% 2.59/1.01  --splitting_mode                        input
% 2.59/1.01  --splitting_grd                         true
% 2.59/1.01  --splitting_cvd                         false
% 2.59/1.01  --splitting_cvd_svl                     false
% 2.59/1.01  --splitting_nvd                         32
% 2.59/1.01  --sub_typing                            true
% 2.59/1.01  --prep_gs_sim                           true
% 2.59/1.01  --prep_unflatten                        true
% 2.59/1.01  --prep_res_sim                          true
% 2.59/1.01  --prep_upred                            true
% 2.59/1.01  --prep_sem_filter                       exhaustive
% 2.59/1.01  --prep_sem_filter_out                   false
% 2.59/1.01  --pred_elim                             true
% 2.59/1.01  --res_sim_input                         true
% 2.59/1.01  --eq_ax_congr_red                       true
% 2.59/1.01  --pure_diseq_elim                       true
% 2.59/1.01  --brand_transform                       false
% 2.59/1.01  --non_eq_to_eq                          false
% 2.59/1.01  --prep_def_merge                        true
% 2.59/1.01  --prep_def_merge_prop_impl              false
% 2.59/1.01  --prep_def_merge_mbd                    true
% 2.59/1.01  --prep_def_merge_tr_red                 false
% 2.59/1.01  --prep_def_merge_tr_cl                  false
% 2.59/1.01  --smt_preprocessing                     true
% 2.59/1.01  --smt_ac_axioms                         fast
% 2.59/1.01  --preprocessed_out                      false
% 2.59/1.01  --preprocessed_stats                    false
% 2.59/1.01  
% 2.59/1.01  ------ Abstraction refinement Options
% 2.59/1.01  
% 2.59/1.01  --abstr_ref                             []
% 2.59/1.01  --abstr_ref_prep                        false
% 2.59/1.01  --abstr_ref_until_sat                   false
% 2.59/1.01  --abstr_ref_sig_restrict                funpre
% 2.59/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/1.01  --abstr_ref_under                       []
% 2.59/1.01  
% 2.59/1.01  ------ SAT Options
% 2.59/1.01  
% 2.59/1.01  --sat_mode                              false
% 2.59/1.01  --sat_fm_restart_options                ""
% 2.59/1.01  --sat_gr_def                            false
% 2.59/1.01  --sat_epr_types                         true
% 2.59/1.01  --sat_non_cyclic_types                  false
% 2.59/1.01  --sat_finite_models                     false
% 2.59/1.01  --sat_fm_lemmas                         false
% 2.59/1.01  --sat_fm_prep                           false
% 2.59/1.01  --sat_fm_uc_incr                        true
% 2.59/1.01  --sat_out_model                         small
% 2.59/1.01  --sat_out_clauses                       false
% 2.59/1.01  
% 2.59/1.01  ------ QBF Options
% 2.59/1.01  
% 2.59/1.01  --qbf_mode                              false
% 2.59/1.01  --qbf_elim_univ                         false
% 2.59/1.01  --qbf_dom_inst                          none
% 2.59/1.01  --qbf_dom_pre_inst                      false
% 2.59/1.01  --qbf_sk_in                             false
% 2.59/1.01  --qbf_pred_elim                         true
% 2.59/1.01  --qbf_split                             512
% 2.59/1.01  
% 2.59/1.01  ------ BMC1 Options
% 2.59/1.01  
% 2.59/1.01  --bmc1_incremental                      false
% 2.59/1.01  --bmc1_axioms                           reachable_all
% 2.59/1.01  --bmc1_min_bound                        0
% 2.59/1.01  --bmc1_max_bound                        -1
% 2.59/1.01  --bmc1_max_bound_default                -1
% 2.59/1.01  --bmc1_symbol_reachability              true
% 2.59/1.01  --bmc1_property_lemmas                  false
% 2.59/1.01  --bmc1_k_induction                      false
% 2.59/1.01  --bmc1_non_equiv_states                 false
% 2.59/1.01  --bmc1_deadlock                         false
% 2.59/1.01  --bmc1_ucm                              false
% 2.59/1.01  --bmc1_add_unsat_core                   none
% 2.59/1.01  --bmc1_unsat_core_children              false
% 2.59/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/1.01  --bmc1_out_stat                         full
% 2.59/1.01  --bmc1_ground_init                      false
% 2.59/1.01  --bmc1_pre_inst_next_state              false
% 2.59/1.01  --bmc1_pre_inst_state                   false
% 2.59/1.01  --bmc1_pre_inst_reach_state             false
% 2.59/1.01  --bmc1_out_unsat_core                   false
% 2.59/1.01  --bmc1_aig_witness_out                  false
% 2.59/1.01  --bmc1_verbose                          false
% 2.59/1.01  --bmc1_dump_clauses_tptp                false
% 2.59/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.59/1.01  --bmc1_dump_file                        -
% 2.59/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.59/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.59/1.01  --bmc1_ucm_extend_mode                  1
% 2.59/1.01  --bmc1_ucm_init_mode                    2
% 2.59/1.01  --bmc1_ucm_cone_mode                    none
% 2.59/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.59/1.01  --bmc1_ucm_relax_model                  4
% 2.59/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.59/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/1.01  --bmc1_ucm_layered_model                none
% 2.59/1.01  --bmc1_ucm_max_lemma_size               10
% 2.59/1.01  
% 2.59/1.01  ------ AIG Options
% 2.59/1.01  
% 2.59/1.01  --aig_mode                              false
% 2.59/1.01  
% 2.59/1.01  ------ Instantiation Options
% 2.59/1.01  
% 2.59/1.01  --instantiation_flag                    true
% 2.59/1.01  --inst_sos_flag                         false
% 2.59/1.01  --inst_sos_phase                        true
% 2.59/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/1.01  --inst_lit_sel_side                     none
% 2.59/1.01  --inst_solver_per_active                1400
% 2.59/1.01  --inst_solver_calls_frac                1.
% 2.59/1.01  --inst_passive_queue_type               priority_queues
% 2.59/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/1.01  --inst_passive_queues_freq              [25;2]
% 2.59/1.01  --inst_dismatching                      true
% 2.59/1.01  --inst_eager_unprocessed_to_passive     true
% 2.59/1.01  --inst_prop_sim_given                   true
% 2.59/1.01  --inst_prop_sim_new                     false
% 2.59/1.01  --inst_subs_new                         false
% 2.59/1.01  --inst_eq_res_simp                      false
% 2.59/1.01  --inst_subs_given                       false
% 2.59/1.01  --inst_orphan_elimination               true
% 2.59/1.01  --inst_learning_loop_flag               true
% 2.59/1.01  --inst_learning_start                   3000
% 2.59/1.01  --inst_learning_factor                  2
% 2.59/1.01  --inst_start_prop_sim_after_learn       3
% 2.59/1.01  --inst_sel_renew                        solver
% 2.59/1.01  --inst_lit_activity_flag                true
% 2.59/1.01  --inst_restr_to_given                   false
% 2.59/1.01  --inst_activity_threshold               500
% 2.59/1.01  --inst_out_proof                        true
% 2.59/1.01  
% 2.59/1.01  ------ Resolution Options
% 2.59/1.01  
% 2.59/1.01  --resolution_flag                       false
% 2.59/1.01  --res_lit_sel                           adaptive
% 2.59/1.01  --res_lit_sel_side                      none
% 2.59/1.01  --res_ordering                          kbo
% 2.59/1.01  --res_to_prop_solver                    active
% 2.59/1.01  --res_prop_simpl_new                    false
% 2.59/1.01  --res_prop_simpl_given                  true
% 2.59/1.01  --res_passive_queue_type                priority_queues
% 2.59/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/1.01  --res_passive_queues_freq               [15;5]
% 2.59/1.01  --res_forward_subs                      full
% 2.59/1.01  --res_backward_subs                     full
% 2.59/1.01  --res_forward_subs_resolution           true
% 2.59/1.01  --res_backward_subs_resolution          true
% 2.59/1.01  --res_orphan_elimination                true
% 2.59/1.01  --res_time_limit                        2.
% 2.59/1.01  --res_out_proof                         true
% 2.59/1.01  
% 2.59/1.01  ------ Superposition Options
% 2.59/1.01  
% 2.59/1.01  --superposition_flag                    true
% 2.59/1.01  --sup_passive_queue_type                priority_queues
% 2.59/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.59/1.01  --demod_completeness_check              fast
% 2.59/1.01  --demod_use_ground                      true
% 2.59/1.01  --sup_to_prop_solver                    passive
% 2.59/1.01  --sup_prop_simpl_new                    true
% 2.59/1.01  --sup_prop_simpl_given                  true
% 2.59/1.01  --sup_fun_splitting                     false
% 2.59/1.01  --sup_smt_interval                      50000
% 2.59/1.01  
% 2.59/1.01  ------ Superposition Simplification Setup
% 2.59/1.01  
% 2.59/1.01  --sup_indices_passive                   []
% 2.59/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/1.01  --sup_full_bw                           [BwDemod]
% 2.59/1.01  --sup_immed_triv                        [TrivRules]
% 2.59/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/1.01  --sup_immed_bw_main                     []
% 2.59/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/1.01  
% 2.59/1.01  ------ Combination Options
% 2.59/1.01  
% 2.59/1.01  --comb_res_mult                         3
% 2.59/1.01  --comb_sup_mult                         2
% 2.59/1.01  --comb_inst_mult                        10
% 2.59/1.01  
% 2.59/1.01  ------ Debug Options
% 2.59/1.01  
% 2.59/1.01  --dbg_backtrace                         false
% 2.59/1.01  --dbg_dump_prop_clauses                 false
% 2.59/1.01  --dbg_dump_prop_clauses_file            -
% 2.59/1.01  --dbg_out_stat                          false
% 2.59/1.01  
% 2.59/1.01  
% 2.59/1.01  
% 2.59/1.01  
% 2.59/1.01  ------ Proving...
% 2.59/1.01  
% 2.59/1.01  
% 2.59/1.01  % SZS status Theorem for theBenchmark.p
% 2.59/1.01  
% 2.59/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.59/1.01  
% 2.59/1.01  fof(f4,axiom,(
% 2.59/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 2.59/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.01  
% 2.59/1.01  fof(f12,plain,(
% 2.59/1.01    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 2.59/1.01    inference(ennf_transformation,[],[f4])).
% 2.59/1.01  
% 2.59/1.01  fof(f18,plain,(
% 2.59/1.01    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.59/1.01    inference(nnf_transformation,[],[f12])).
% 2.59/1.01  
% 2.59/1.01  fof(f19,plain,(
% 2.59/1.01    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.59/1.01    inference(rectify,[],[f18])).
% 2.59/1.01  
% 2.59/1.01  fof(f22,plain,(
% 2.59/1.01    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)))),
% 2.59/1.01    introduced(choice_axiom,[])).
% 2.59/1.01  
% 2.59/1.01  fof(f21,plain,(
% 2.59/1.01    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(X3,sK1(X0,X1,X2)),X0)))) )),
% 2.59/1.01    introduced(choice_axiom,[])).
% 2.59/1.01  
% 2.59/1.01  fof(f20,plain,(
% 2.59/1.01    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.59/1.01    introduced(choice_axiom,[])).
% 2.59/1.01  
% 2.59/1.01  fof(f23,plain,(
% 2.59/1.01    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.59/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22,f21,f20])).
% 2.59/1.01  
% 2.59/1.01  fof(f37,plain,(
% 2.59/1.01    ( ! [X6,X2,X0,X1] : (r2_hidden(sK2(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 2.59/1.01    inference(cnf_transformation,[],[f23])).
% 2.59/1.01  
% 2.59/1.01  fof(f51,plain,(
% 2.59/1.01    ( ! [X6,X0,X1] : (r2_hidden(sK2(X0,X1,X6),X1) | ~r2_hidden(X6,k10_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.59/1.01    inference(equality_resolution,[],[f37])).
% 2.59/1.01  
% 2.59/1.01  fof(f36,plain,(
% 2.59/1.01    ( ! [X6,X2,X0,X1] : (r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 2.59/1.01    inference(cnf_transformation,[],[f23])).
% 2.59/1.01  
% 2.59/1.01  fof(f52,plain,(
% 2.59/1.01    ( ! [X6,X0,X1] : (r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) | ~r2_hidden(X6,k10_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.59/1.01    inference(equality_resolution,[],[f36])).
% 2.59/1.01  
% 2.59/1.01  fof(f7,conjecture,(
% 2.59/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 2.59/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.01  
% 2.59/1.01  fof(f8,negated_conjecture,(
% 2.59/1.01    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 2.59/1.01    inference(negated_conjecture,[],[f7])).
% 2.59/1.01  
% 2.59/1.01  fof(f9,plain,(
% 2.59/1.01    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)))))),
% 2.59/1.01    inference(pure_predicate_removal,[],[f8])).
% 2.59/1.01  
% 2.59/1.01  fof(f15,plain,(
% 2.59/1.01    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.59/1.01    inference(ennf_transformation,[],[f9])).
% 2.59/1.01  
% 2.59/1.01  fof(f24,plain,(
% 2.59/1.01    ? [X0,X1,X2,X3] : (? [X4] : (((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.59/1.01    inference(nnf_transformation,[],[f15])).
% 2.59/1.01  
% 2.59/1.01  fof(f25,plain,(
% 2.59/1.01    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.59/1.01    inference(flattening,[],[f24])).
% 2.59/1.01  
% 2.59/1.01  fof(f26,plain,(
% 2.59/1.01    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.59/1.01    inference(rectify,[],[f25])).
% 2.59/1.01  
% 2.59/1.01  fof(f29,plain,(
% 2.59/1.01    ( ! [X4,X2,X3,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK8,X1) & r2_hidden(k4_tarski(X4,sK8),X3) & m1_subset_1(sK8,X2))) )),
% 2.59/1.01    introduced(choice_axiom,[])).
% 2.59/1.01  
% 2.59/1.01  fof(f28,plain,(
% 2.59/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) => ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(sK7,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(sK7,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(sK7,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(sK7,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(sK7,X0))) )),
% 2.59/1.01    introduced(choice_axiom,[])).
% 2.59/1.01  
% 2.59/1.01  fof(f27,plain,(
% 2.59/1.01    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (? [X4] : ((! [X5] : (~r2_hidden(X5,sK4) | ~r2_hidden(k4_tarski(X4,X5),sK6) | ~m1_subset_1(X5,sK5)) | ~r2_hidden(X4,k8_relset_1(sK3,sK5,sK6,sK4))) & (? [X6] : (r2_hidden(X6,sK4) & r2_hidden(k4_tarski(X4,X6),sK6) & m1_subset_1(X6,sK5)) | r2_hidden(X4,k8_relset_1(sK3,sK5,sK6,sK4))) & m1_subset_1(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))))),
% 2.59/1.01    introduced(choice_axiom,[])).
% 2.59/1.01  
% 2.59/1.01  fof(f30,plain,(
% 2.59/1.01    ((! [X5] : (~r2_hidden(X5,sK4) | ~r2_hidden(k4_tarski(sK7,X5),sK6) | ~m1_subset_1(X5,sK5)) | ~r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4))) & ((r2_hidden(sK8,sK4) & r2_hidden(k4_tarski(sK7,sK8),sK6) & m1_subset_1(sK8,sK5)) | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4))) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))),
% 2.59/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f26,f29,f28,f27])).
% 2.59/1.01  
% 2.59/1.01  fof(f44,plain,(
% 2.59/1.01    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))),
% 2.59/1.01    inference(cnf_transformation,[],[f30])).
% 2.59/1.01  
% 2.59/1.01  fof(f2,axiom,(
% 2.59/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.59/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.01  
% 2.59/1.01  fof(f10,plain,(
% 2.59/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.59/1.01    inference(ennf_transformation,[],[f2])).
% 2.59/1.01  
% 2.59/1.01  fof(f34,plain,(
% 2.59/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.59/1.01    inference(cnf_transformation,[],[f10])).
% 2.59/1.01  
% 2.59/1.01  fof(f1,axiom,(
% 2.59/1.01    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.59/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.01  
% 2.59/1.01  fof(f16,plain,(
% 2.59/1.01    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.59/1.01    inference(nnf_transformation,[],[f1])).
% 2.59/1.01  
% 2.59/1.01  fof(f17,plain,(
% 2.59/1.01    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.59/1.01    inference(flattening,[],[f16])).
% 2.59/1.01  
% 2.59/1.01  fof(f32,plain,(
% 2.59/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.59/1.01    inference(cnf_transformation,[],[f17])).
% 2.59/1.01  
% 2.59/1.01  fof(f5,axiom,(
% 2.59/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.59/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.01  
% 2.59/1.01  fof(f13,plain,(
% 2.59/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/1.01    inference(ennf_transformation,[],[f5])).
% 2.59/1.01  
% 2.59/1.01  fof(f42,plain,(
% 2.59/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.59/1.01    inference(cnf_transformation,[],[f13])).
% 2.59/1.01  
% 2.59/1.01  fof(f3,axiom,(
% 2.59/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.59/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.01  
% 2.59/1.01  fof(f11,plain,(
% 2.59/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.59/1.01    inference(ennf_transformation,[],[f3])).
% 2.59/1.01  
% 2.59/1.01  fof(f35,plain,(
% 2.59/1.01    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.59/1.01    inference(cnf_transformation,[],[f11])).
% 2.59/1.01  
% 2.59/1.01  fof(f46,plain,(
% 2.59/1.01    m1_subset_1(sK8,sK5) | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4))),
% 2.59/1.01    inference(cnf_transformation,[],[f30])).
% 2.59/1.01  
% 2.59/1.01  fof(f49,plain,(
% 2.59/1.01    ( ! [X5] : (~r2_hidden(X5,sK4) | ~r2_hidden(k4_tarski(sK7,X5),sK6) | ~m1_subset_1(X5,sK5) | ~r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4))) )),
% 2.59/1.01    inference(cnf_transformation,[],[f30])).
% 2.59/1.01  
% 2.59/1.01  fof(f6,axiom,(
% 2.59/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.59/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/1.01  
% 2.59/1.01  fof(f14,plain,(
% 2.59/1.01    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/1.01    inference(ennf_transformation,[],[f6])).
% 2.59/1.01  
% 2.59/1.01  fof(f43,plain,(
% 2.59/1.01    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.59/1.01    inference(cnf_transformation,[],[f14])).
% 2.59/1.01  
% 2.59/1.01  fof(f47,plain,(
% 2.59/1.01    r2_hidden(k4_tarski(sK7,sK8),sK6) | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4))),
% 2.59/1.01    inference(cnf_transformation,[],[f30])).
% 2.59/1.01  
% 2.59/1.01  fof(f38,plain,(
% 2.59/1.01    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 2.59/1.01    inference(cnf_transformation,[],[f23])).
% 2.59/1.01  
% 2.59/1.01  fof(f50,plain,(
% 2.59/1.01    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k10_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~v1_relat_1(X0)) )),
% 2.59/1.01    inference(equality_resolution,[],[f38])).
% 2.59/1.01  
% 2.59/1.01  fof(f48,plain,(
% 2.59/1.01    r2_hidden(sK8,sK4) | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4))),
% 2.59/1.01    inference(cnf_transformation,[],[f30])).
% 2.59/1.01  
% 2.59/1.01  cnf(c_9,plain,
% 2.59/1.01      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 2.59/1.01      | r2_hidden(sK2(X1,X2,X0),X2)
% 2.59/1.01      | ~ v1_relat_1(X1) ),
% 2.59/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_924,plain,
% 2.59/1.01      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 2.59/1.01      | r2_hidden(sK2(X1,X2,X0),X2) = iProver_top
% 2.59/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.59/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_10,plain,
% 2.59/1.01      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 2.59/1.01      | r2_hidden(k4_tarski(X0,sK2(X1,X2,X0)),X1)
% 2.59/1.01      | ~ v1_relat_1(X1) ),
% 2.59/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_923,plain,
% 2.59/1.01      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 2.59/1.01      | r2_hidden(k4_tarski(X0,sK2(X1,X2,X0)),X1) = iProver_top
% 2.59/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.59/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_18,negated_conjecture,
% 2.59/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
% 2.59/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_915,plain,
% 2.59/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) = iProver_top ),
% 2.59/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_3,plain,
% 2.59/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.59/1.01      | ~ r2_hidden(X2,X0)
% 2.59/1.01      | r2_hidden(X2,X1) ),
% 2.59/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_930,plain,
% 2.59/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.59/1.01      | r2_hidden(X2,X0) != iProver_top
% 2.59/1.01      | r2_hidden(X2,X1) = iProver_top ),
% 2.59/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_2033,plain,
% 2.59/1.01      ( r2_hidden(X0,k2_zfmisc_1(sK3,sK5)) = iProver_top
% 2.59/1.01      | r2_hidden(X0,sK6) != iProver_top ),
% 2.59/1.01      inference(superposition,[status(thm)],[c_915,c_930]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_1,plain,
% 2.59/1.01      ( r2_hidden(X0,X1)
% 2.59/1.01      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 2.59/1.01      inference(cnf_transformation,[],[f32]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_932,plain,
% 2.59/1.01      ( r2_hidden(X0,X1) = iProver_top
% 2.59/1.01      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 2.59/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_2245,plain,
% 2.59/1.01      ( r2_hidden(X0,sK5) = iProver_top
% 2.59/1.01      | r2_hidden(k4_tarski(X1,X0),sK6) != iProver_top ),
% 2.59/1.01      inference(superposition,[status(thm)],[c_2033,c_932]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_2580,plain,
% 2.59/1.01      ( r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top
% 2.59/1.01      | r2_hidden(sK2(sK6,X1,X0),sK5) = iProver_top
% 2.59/1.01      | v1_relat_1(sK6) != iProver_top ),
% 2.59/1.01      inference(superposition,[status(thm)],[c_923,c_2245]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_19,plain,
% 2.59/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) = iProver_top ),
% 2.59/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_11,plain,
% 2.59/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/1.01      | v1_relat_1(X0) ),
% 2.59/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_1079,plain,
% 2.59/1.01      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 2.59/1.01      | v1_relat_1(sK6) ),
% 2.59/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_1080,plain,
% 2.59/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top
% 2.59/1.01      | v1_relat_1(sK6) = iProver_top ),
% 2.59/1.01      inference(predicate_to_equality,[status(thm)],[c_1079]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_3729,plain,
% 2.59/1.01      ( r2_hidden(sK2(sK6,X1,X0),sK5) = iProver_top
% 2.59/1.01      | r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top ),
% 2.59/1.01      inference(global_propositional_subsumption,
% 2.59/1.01                [status(thm)],
% 2.59/1.01                [c_2580,c_19,c_1080]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_3730,plain,
% 2.59/1.01      ( r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top
% 2.59/1.01      | r2_hidden(sK2(sK6,X1,X0),sK5) = iProver_top ),
% 2.59/1.01      inference(renaming,[status(thm)],[c_3729]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_4,plain,
% 2.59/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.59/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_929,plain,
% 2.59/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 2.59/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 2.59/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_3737,plain,
% 2.59/1.01      ( m1_subset_1(sK2(sK6,X0,X1),sK5) = iProver_top
% 2.59/1.01      | r2_hidden(X1,k10_relat_1(sK6,X0)) != iProver_top ),
% 2.59/1.01      inference(superposition,[status(thm)],[c_3730,c_929]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_16,negated_conjecture,
% 2.59/1.01      ( m1_subset_1(sK8,sK5)
% 2.59/1.01      | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) ),
% 2.59/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_917,plain,
% 2.59/1.01      ( m1_subset_1(sK8,sK5) = iProver_top
% 2.59/1.01      | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) = iProver_top ),
% 2.59/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_13,negated_conjecture,
% 2.59/1.01      ( ~ m1_subset_1(X0,sK5)
% 2.59/1.01      | ~ r2_hidden(X0,sK4)
% 2.59/1.01      | ~ r2_hidden(k4_tarski(sK7,X0),sK6)
% 2.59/1.01      | ~ r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) ),
% 2.59/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_920,plain,
% 2.59/1.01      ( m1_subset_1(X0,sK5) != iProver_top
% 2.59/1.01      | r2_hidden(X0,sK4) != iProver_top
% 2.59/1.01      | r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top
% 2.59/1.01      | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) != iProver_top ),
% 2.59/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_1119,plain,
% 2.59/1.01      ( m1_subset_1(X0,sK5) != iProver_top
% 2.59/1.01      | m1_subset_1(sK8,sK5) = iProver_top
% 2.59/1.01      | r2_hidden(X0,sK4) != iProver_top
% 2.59/1.01      | r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top ),
% 2.59/1.01      inference(superposition,[status(thm)],[c_917,c_920]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_1837,plain,
% 2.59/1.01      ( m1_subset_1(sK2(sK6,X0,sK7),sK5) != iProver_top
% 2.59/1.01      | m1_subset_1(sK8,sK5) = iProver_top
% 2.59/1.01      | r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top
% 2.59/1.01      | v1_relat_1(sK6) != iProver_top ),
% 2.59/1.01      inference(superposition,[status(thm)],[c_923,c_1119]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_2969,plain,
% 2.59/1.01      ( r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top
% 2.59/1.01      | r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
% 2.59/1.01      | m1_subset_1(sK8,sK5) = iProver_top
% 2.59/1.01      | m1_subset_1(sK2(sK6,X0,sK7),sK5) != iProver_top ),
% 2.59/1.01      inference(global_propositional_subsumption,
% 2.59/1.01                [status(thm)],
% 2.59/1.01                [c_1837,c_19,c_1080]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_2970,plain,
% 2.59/1.01      ( m1_subset_1(sK2(sK6,X0,sK7),sK5) != iProver_top
% 2.59/1.01      | m1_subset_1(sK8,sK5) = iProver_top
% 2.59/1.01      | r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top ),
% 2.59/1.01      inference(renaming,[status(thm)],[c_2969]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_4232,plain,
% 2.59/1.01      ( m1_subset_1(sK8,sK5) = iProver_top
% 2.59/1.01      | r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top ),
% 2.59/1.01      inference(superposition,[status(thm)],[c_3737,c_2970]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_12,plain,
% 2.59/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/1.01      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.59/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_921,plain,
% 2.59/1.01      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.59/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.59/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_1508,plain,
% 2.59/1.01      ( k8_relset_1(sK3,sK5,sK6,X0) = k10_relat_1(sK6,X0) ),
% 2.59/1.01      inference(superposition,[status(thm)],[c_915,c_921]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_15,negated_conjecture,
% 2.59/1.01      ( r2_hidden(k4_tarski(sK7,sK8),sK6)
% 2.59/1.01      | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) ),
% 2.59/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_918,plain,
% 2.59/1.01      ( r2_hidden(k4_tarski(sK7,sK8),sK6) = iProver_top
% 2.59/1.01      | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) = iProver_top ),
% 2.59/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_1672,plain,
% 2.59/1.01      ( r2_hidden(k4_tarski(sK7,sK8),sK6) = iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top ),
% 2.59/1.01      inference(demodulation,[status(thm)],[c_1508,c_918]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_8,plain,
% 2.59/1.01      ( ~ r2_hidden(X0,X1)
% 2.59/1.01      | r2_hidden(X2,k10_relat_1(X3,X1))
% 2.59/1.01      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 2.59/1.01      | ~ v1_relat_1(X3) ),
% 2.59/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_925,plain,
% 2.59/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.59/1.01      | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
% 2.59/1.01      | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
% 2.59/1.01      | v1_relat_1(X3) != iProver_top ),
% 2.59/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_2247,plain,
% 2.59/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.59/1.01      | r2_hidden(X2,k10_relat_1(k2_zfmisc_1(sK3,sK5),X1)) = iProver_top
% 2.59/1.01      | r2_hidden(k4_tarski(X2,X0),sK6) != iProver_top
% 2.59/1.01      | v1_relat_1(k2_zfmisc_1(sK3,sK5)) != iProver_top ),
% 2.59/1.01      inference(superposition,[status(thm)],[c_2033,c_925]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_2656,plain,
% 2.59/1.01      ( r2_hidden(sK8,X0) != iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(k2_zfmisc_1(sK3,sK5),X0)) = iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top
% 2.59/1.01      | v1_relat_1(k2_zfmisc_1(sK3,sK5)) != iProver_top ),
% 2.59/1.01      inference(superposition,[status(thm)],[c_1672,c_2247]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_14,negated_conjecture,
% 2.59/1.01      ( r2_hidden(sK8,sK4)
% 2.59/1.01      | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) ),
% 2.59/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_919,plain,
% 2.59/1.01      ( r2_hidden(sK8,sK4) = iProver_top
% 2.59/1.01      | r2_hidden(sK7,k8_relset_1(sK3,sK5,sK6,sK4)) = iProver_top ),
% 2.59/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_1673,plain,
% 2.59/1.01      ( r2_hidden(sK8,sK4) = iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top ),
% 2.59/1.01      inference(demodulation,[status(thm)],[c_1508,c_919]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_2284,plain,
% 2.59/1.01      ( r2_hidden(sK8,X0) != iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,X0)) = iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top
% 2.59/1.01      | v1_relat_1(sK6) != iProver_top ),
% 2.59/1.01      inference(superposition,[status(thm)],[c_1672,c_925]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_3207,plain,
% 2.59/1.01      ( r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,X0)) = iProver_top
% 2.59/1.01      | r2_hidden(sK8,X0) != iProver_top ),
% 2.59/1.01      inference(global_propositional_subsumption,
% 2.59/1.01                [status(thm)],
% 2.59/1.01                [c_2284,c_19,c_1080]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_3208,plain,
% 2.59/1.01      ( r2_hidden(sK8,X0) != iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,X0)) = iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top ),
% 2.59/1.01      inference(renaming,[status(thm)],[c_3207]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_3218,plain,
% 2.59/1.01      ( r2_hidden(sK8,sK4) != iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top
% 2.59/1.01      | iProver_top != iProver_top ),
% 2.59/1.01      inference(equality_factoring,[status(thm)],[c_3208]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_3220,plain,
% 2.59/1.01      ( r2_hidden(sK8,sK4) != iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top ),
% 2.59/1.01      inference(equality_resolution_simp,[status(thm)],[c_3218]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_3672,plain,
% 2.59/1.01      ( r2_hidden(sK7,k10_relat_1(sK6,sK4)) = iProver_top ),
% 2.59/1.01      inference(global_propositional_subsumption,
% 2.59/1.01                [status(thm)],
% 2.59/1.01                [c_2656,c_1673,c_3220]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_1675,plain,
% 2.59/1.01      ( m1_subset_1(X0,sK5) != iProver_top
% 2.59/1.01      | r2_hidden(X0,sK4) != iProver_top
% 2.59/1.01      | r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,sK4)) != iProver_top ),
% 2.59/1.01      inference(demodulation,[status(thm)],[c_1508,c_920]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_1834,plain,
% 2.59/1.01      ( m1_subset_1(sK2(sK6,X0,sK7),sK5) != iProver_top
% 2.59/1.01      | r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,sK4)) != iProver_top
% 2.59/1.01      | v1_relat_1(sK6) != iProver_top ),
% 2.59/1.01      inference(superposition,[status(thm)],[c_923,c_1675]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_3011,plain,
% 2.59/1.01      ( r2_hidden(sK7,k10_relat_1(sK6,sK4)) != iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top
% 2.59/1.01      | r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
% 2.59/1.01      | m1_subset_1(sK2(sK6,X0,sK7),sK5) != iProver_top ),
% 2.59/1.01      inference(global_propositional_subsumption,
% 2.59/1.01                [status(thm)],
% 2.59/1.01                [c_1834,c_19,c_1080]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_3012,plain,
% 2.59/1.01      ( m1_subset_1(sK2(sK6,X0,sK7),sK5) != iProver_top
% 2.59/1.01      | r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,sK4)) != iProver_top ),
% 2.59/1.01      inference(renaming,[status(thm)],[c_3011]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_4230,plain,
% 2.59/1.01      ( r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,sK4)) != iProver_top ),
% 2.59/1.01      inference(superposition,[status(thm)],[c_3737,c_3012]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_5151,plain,
% 2.59/1.01      ( r2_hidden(sK2(sK6,X0,sK7),sK4) != iProver_top
% 2.59/1.01      | r2_hidden(sK7,k10_relat_1(sK6,X0)) != iProver_top ),
% 2.59/1.01      inference(global_propositional_subsumption,
% 2.59/1.01                [status(thm)],
% 2.59/1.01                [c_4232,c_1673,c_3220,c_4230]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(c_5159,plain,
% 2.59/1.01      ( r2_hidden(sK7,k10_relat_1(sK6,sK4)) != iProver_top
% 2.59/1.01      | v1_relat_1(sK6) != iProver_top ),
% 2.59/1.01      inference(superposition,[status(thm)],[c_924,c_5151]) ).
% 2.59/1.01  
% 2.59/1.01  cnf(contradiction,plain,
% 2.59/1.01      ( $false ),
% 2.59/1.01      inference(minisat,[status(thm)],[c_5159,c_3672,c_1080,c_19]) ).
% 2.59/1.01  
% 2.59/1.01  
% 2.59/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.59/1.01  
% 2.59/1.01  ------                               Statistics
% 2.59/1.01  
% 2.59/1.01  ------ General
% 2.59/1.01  
% 2.59/1.01  abstr_ref_over_cycles:                  0
% 2.59/1.01  abstr_ref_under_cycles:                 0
% 2.59/1.01  gc_basic_clause_elim:                   0
% 2.59/1.01  forced_gc_time:                         0
% 2.59/1.01  parsing_time:                           0.009
% 2.59/1.01  unif_index_cands_time:                  0.
% 2.59/1.01  unif_index_add_time:                    0.
% 2.59/1.01  orderings_time:                         0.
% 2.59/1.01  out_proof_time:                         0.008
% 2.59/1.01  total_time:                             0.184
% 2.59/1.01  num_of_symbols:                         48
% 2.59/1.01  num_of_terms:                           6709
% 2.59/1.01  
% 2.59/1.01  ------ Preprocessing
% 2.59/1.01  
% 2.59/1.01  num_of_splits:                          0
% 2.59/1.01  num_of_split_atoms:                     0
% 2.59/1.01  num_of_reused_defs:                     0
% 2.59/1.01  num_eq_ax_congr_red:                    24
% 2.59/1.01  num_of_sem_filtered_clauses:            1
% 2.59/1.01  num_of_subtypes:                        0
% 2.59/1.01  monotx_restored_types:                  0
% 2.59/1.01  sat_num_of_epr_types:                   0
% 2.59/1.01  sat_num_of_non_cyclic_types:            0
% 2.59/1.01  sat_guarded_non_collapsed_types:        0
% 2.59/1.01  num_pure_diseq_elim:                    0
% 2.59/1.01  simp_replaced_by:                       0
% 2.59/1.01  res_preprocessed:                       74
% 2.59/1.01  prep_upred:                             0
% 2.59/1.01  prep_unflattend:                        24
% 2.59/1.01  smt_new_axioms:                         0
% 2.59/1.01  pred_elim_cands:                        3
% 2.59/1.01  pred_elim:                              0
% 2.59/1.01  pred_elim_cl:                           0
% 2.59/1.01  pred_elim_cycles:                       2
% 2.59/1.01  merged_defs:                            0
% 2.59/1.01  merged_defs_ncl:                        0
% 2.59/1.01  bin_hyper_res:                          0
% 2.59/1.01  prep_cycles:                            3
% 2.59/1.01  pred_elim_time:                         0.007
% 2.59/1.01  splitting_time:                         0.
% 2.59/1.01  sem_filter_time:                        0.
% 2.59/1.01  monotx_time:                            0.
% 2.59/1.01  subtype_inf_time:                       0.
% 2.59/1.01  
% 2.59/1.01  ------ Problem properties
% 2.59/1.01  
% 2.59/1.01  clauses:                                19
% 2.59/1.01  conjectures:                            6
% 2.59/1.01  epr:                                    2
% 2.59/1.01  horn:                                   14
% 2.59/1.01  ground:                                 5
% 2.59/1.01  unary:                                  2
% 2.59/1.01  binary:                                 8
% 2.59/1.01  lits:                                   51
% 2.59/1.01  lits_eq:                                4
% 2.59/1.01  fd_pure:                                0
% 2.59/1.01  fd_pseudo:                              0
% 2.59/1.01  fd_cond:                                0
% 2.59/1.01  fd_pseudo_cond:                         3
% 2.59/1.01  ac_symbols:                             0
% 2.59/1.01  
% 2.59/1.01  ------ Propositional Solver
% 2.59/1.01  
% 2.59/1.01  prop_solver_calls:                      24
% 2.59/1.01  prop_fast_solver_calls:                 711
% 2.59/1.01  smt_solver_calls:                       0
% 2.59/1.01  smt_fast_solver_calls:                  0
% 2.59/1.01  prop_num_of_clauses:                    2245
% 2.59/1.01  prop_preprocess_simplified:             4588
% 2.59/1.01  prop_fo_subsumed:                       18
% 2.59/1.01  prop_solver_time:                       0.
% 2.59/1.01  smt_solver_time:                        0.
% 2.59/1.01  smt_fast_solver_time:                   0.
% 2.59/1.01  prop_fast_solver_time:                  0.
% 2.59/1.01  prop_unsat_core_time:                   0.
% 2.59/1.01  
% 2.59/1.01  ------ QBF
% 2.59/1.01  
% 2.59/1.01  qbf_q_res:                              0
% 2.59/1.01  qbf_num_tautologies:                    0
% 2.59/1.01  qbf_prep_cycles:                        0
% 2.59/1.01  
% 2.59/1.01  ------ BMC1
% 2.59/1.01  
% 2.59/1.01  bmc1_current_bound:                     -1
% 2.59/1.01  bmc1_last_solved_bound:                 -1
% 2.59/1.01  bmc1_unsat_core_size:                   -1
% 2.59/1.01  bmc1_unsat_core_parents_size:           -1
% 2.59/1.01  bmc1_merge_next_fun:                    0
% 2.59/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.59/1.01  
% 2.59/1.01  ------ Instantiation
% 2.59/1.01  
% 2.59/1.01  inst_num_of_clauses:                    576
% 2.59/1.01  inst_num_in_passive:                    278
% 2.59/1.01  inst_num_in_active:                     215
% 2.59/1.01  inst_num_in_unprocessed:                84
% 2.59/1.01  inst_num_of_loops:                      320
% 2.59/1.01  inst_num_of_learning_restarts:          0
% 2.59/1.01  inst_num_moves_active_passive:          101
% 2.59/1.01  inst_lit_activity:                      0
% 2.59/1.01  inst_lit_activity_moves:                0
% 2.59/1.01  inst_num_tautologies:                   0
% 2.59/1.01  inst_num_prop_implied:                  0
% 2.59/1.01  inst_num_existing_simplified:           0
% 2.59/1.01  inst_num_eq_res_simplified:             0
% 2.59/1.01  inst_num_child_elim:                    0
% 2.59/1.01  inst_num_of_dismatching_blockings:      45
% 2.59/1.01  inst_num_of_non_proper_insts:           349
% 2.59/1.01  inst_num_of_duplicates:                 0
% 2.59/1.01  inst_inst_num_from_inst_to_res:         0
% 2.59/1.01  inst_dismatching_checking_time:         0.
% 2.59/1.01  
% 2.59/1.01  ------ Resolution
% 2.59/1.01  
% 2.59/1.01  res_num_of_clauses:                     0
% 2.59/1.01  res_num_in_passive:                     0
% 2.59/1.01  res_num_in_active:                      0
% 2.59/1.01  res_num_of_loops:                       77
% 2.59/1.01  res_forward_subset_subsumed:            17
% 2.59/1.01  res_backward_subset_subsumed:           2
% 2.59/1.01  res_forward_subsumed:                   0
% 2.59/1.01  res_backward_subsumed:                  0
% 2.59/1.01  res_forward_subsumption_resolution:     0
% 2.59/1.01  res_backward_subsumption_resolution:    0
% 2.59/1.01  res_clause_to_clause_subsumption:       243
% 2.59/1.01  res_orphan_elimination:                 0
% 2.59/1.01  res_tautology_del:                      20
% 2.59/1.01  res_num_eq_res_simplified:              0
% 2.59/1.01  res_num_sel_changes:                    0
% 2.59/1.01  res_moves_from_active_to_pass:          0
% 2.59/1.01  
% 2.59/1.01  ------ Superposition
% 2.59/1.01  
% 2.59/1.01  sup_time_total:                         0.
% 2.59/1.01  sup_time_generating:                    0.
% 2.59/1.01  sup_time_sim_full:                      0.
% 2.59/1.01  sup_time_sim_immed:                     0.
% 2.59/1.01  
% 2.59/1.01  sup_num_of_clauses:                     101
% 2.59/1.01  sup_num_in_active:                      53
% 2.59/1.01  sup_num_in_passive:                     48
% 2.59/1.01  sup_num_of_loops:                       62
% 2.59/1.01  sup_fw_superposition:                   40
% 2.59/1.01  sup_bw_superposition:                   65
% 2.59/1.01  sup_immediate_simplified:               7
% 2.59/1.01  sup_given_eliminated:                   0
% 2.59/1.01  comparisons_done:                       0
% 2.59/1.01  comparisons_avoided:                    0
% 2.59/1.01  
% 2.59/1.01  ------ Simplifications
% 2.59/1.01  
% 2.59/1.01  
% 2.59/1.01  sim_fw_subset_subsumed:                 3
% 2.59/1.01  sim_bw_subset_subsumed:                 7
% 2.59/1.01  sim_fw_subsumed:                        1
% 2.59/1.01  sim_bw_subsumed:                        3
% 2.59/1.01  sim_fw_subsumption_res:                 0
% 2.59/1.01  sim_bw_subsumption_res:                 0
% 2.59/1.01  sim_tautology_del:                      6
% 2.59/1.01  sim_eq_tautology_del:                   0
% 2.59/1.01  sim_eq_res_simp:                        1
% 2.59/1.01  sim_fw_demodulated:                     3
% 2.59/1.01  sim_bw_demodulated:                     4
% 2.59/1.01  sim_light_normalised:                   0
% 2.59/1.01  sim_joinable_taut:                      0
% 2.59/1.01  sim_joinable_simp:                      0
% 2.59/1.01  sim_ac_normalised:                      0
% 2.59/1.01  sim_smt_subsumption:                    0
% 2.59/1.01  
%------------------------------------------------------------------------------

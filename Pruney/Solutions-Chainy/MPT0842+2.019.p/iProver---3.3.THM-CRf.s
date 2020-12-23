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
% DateTime   : Thu Dec  3 11:57:06 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 705 expanded)
%              Number of clauses        :   67 ( 234 expanded)
%              Number of leaves         :   18 ( 157 expanded)
%              Depth                    :   20
%              Number of atoms          :  513 (3947 expanded)
%              Number of equality atoms :  141 ( 338 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
        & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
            & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f19,plain,(
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

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f42,plain,(
    ! [X4,X2,X3,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X4,X6),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK10,X1)
        & r2_hidden(k4_tarski(X4,sK10),X3)
        & m1_subset_1(sK10,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
              | ~ r2_hidden(k4_tarski(sK9,X5),X3)
              | ~ m1_subset_1(X5,X2) )
          | ~ r2_hidden(sK9,k8_relset_1(X0,X2,X3,X1)) )
        & ( ? [X6] :
              ( r2_hidden(X6,X1)
              & r2_hidden(k4_tarski(sK9,X6),X3)
              & m1_subset_1(X6,X2) )
          | r2_hidden(sK9,k8_relset_1(X0,X2,X3,X1)) )
        & m1_subset_1(sK9,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
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
                ( ~ r2_hidden(X5,sK6)
                | ~ r2_hidden(k4_tarski(X4,X5),sK8)
                | ~ m1_subset_1(X5,sK7) )
            | ~ r2_hidden(X4,k8_relset_1(sK5,sK7,sK8,sK6)) )
          & ( ? [X6] :
                ( r2_hidden(X6,sK6)
                & r2_hidden(k4_tarski(X4,X6),sK8)
                & m1_subset_1(X6,sK7) )
            | r2_hidden(X4,k8_relset_1(sK5,sK7,sK8,sK6)) )
          & m1_subset_1(X4,sK5) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK7))) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ! [X5] :
          ( ~ r2_hidden(X5,sK6)
          | ~ r2_hidden(k4_tarski(sK9,X5),sK8)
          | ~ m1_subset_1(X5,sK7) )
      | ~ r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) )
    & ( ( r2_hidden(sK10,sK6)
        & r2_hidden(k4_tarski(sK9,sK10),sK8)
        & m1_subset_1(sK10,sK7) )
      | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) )
    & m1_subset_1(sK9,sK5)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK7))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9,sK10])],[f39,f42,f41,f40])).

fof(f66,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK7))) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,
    ( m1_subset_1(sK10,sK7)
    | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK6)
      | ~ r2_hidden(k4_tarski(sK9,X5),sK8)
      | ~ m1_subset_1(X5,sK7)
      | ~ r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,
    ( r2_hidden(k4_tarski(sK9,sK10),sK8)
    | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,
    ( r2_hidden(sK10,sK6)
    | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
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

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
              | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f31,f30,f29])).

fof(f56,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1856,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK7))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1847,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1864,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2600,plain,
    ( r1_tarski(sK8,k2_zfmisc_1(sK5,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1847,c_1864])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK4(X0,X2,X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1855,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4(X0,X2,X1)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1870,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3402,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4(X0,X2,X1)),X3) = iProver_top
    | r1_tarski(X1,X3) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1855,c_1870])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1868,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6497,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X0,X2,X1),X3) = iProver_top
    | r1_tarski(X1,k2_zfmisc_1(X4,X3)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3402,c_1868])).

cnf(c_12423,plain,
    ( r2_hidden(X0,k10_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK8),sK7) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2600,c_6497])).

cnf(c_16,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1857,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_224,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_225,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_224])).

cnf(c_276,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_225])).

cnf(c_1846,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_3334,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK7)) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2600,c_1846])).

cnf(c_3338,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1857,c_3334])).

cnf(c_12485,plain,
    ( r2_hidden(sK4(X0,X1,sK8),sK7) = iProver_top
    | r2_hidden(X0,k10_relat_1(sK8,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12423,c_3338])).

cnf(c_12486,plain,
    ( r2_hidden(X0,k10_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK8),sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_12485])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1866,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_12493,plain,
    ( m1_subset_1(sK4(X0,X1,sK8),sK7) = iProver_top
    | r2_hidden(X0,k10_relat_1(sK8,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12486,c_1866])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK10,sK7)
    | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1849,plain,
    ( m1_subset_1(sK10,sK7) = iProver_top
    | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,negated_conjecture,
    ( ~ m1_subset_1(X0,sK7)
    | ~ r2_hidden(X0,sK6)
    | ~ r2_hidden(k4_tarski(sK9,X0),sK8)
    | ~ r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1852,plain,
    ( m1_subset_1(X0,sK7) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k4_tarski(sK9,X0),sK8) != iProver_top
    | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2193,plain,
    ( m1_subset_1(X0,sK7) != iProver_top
    | m1_subset_1(sK10,sK7) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k4_tarski(sK9,X0),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_1852])).

cnf(c_3380,plain,
    ( m1_subset_1(sK4(sK9,X0,sK8),sK7) != iProver_top
    | m1_subset_1(sK10,sK7) = iProver_top
    | r2_hidden(sK4(sK9,X0,sK8),sK6) != iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,X0)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1855,c_2193])).

cnf(c_3513,plain,
    ( r2_hidden(sK9,k10_relat_1(sK8,X0)) != iProver_top
    | r2_hidden(sK4(sK9,X0,sK8),sK6) != iProver_top
    | m1_subset_1(sK10,sK7) = iProver_top
    | m1_subset_1(sK4(sK9,X0,sK8),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3380,c_3338])).

cnf(c_3514,plain,
    ( m1_subset_1(sK4(sK9,X0,sK8),sK7) != iProver_top
    | m1_subset_1(sK10,sK7) = iProver_top
    | r2_hidden(sK4(sK9,X0,sK8),sK6) != iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3513])).

cnf(c_12504,plain,
    ( m1_subset_1(sK10,sK7) = iProver_top
    | r2_hidden(sK4(sK9,X0,sK8),sK6) != iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12493,c_3514])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1853,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2517,plain,
    ( k8_relset_1(sK5,sK7,sK8,X0) = k10_relat_1(sK8,X0) ),
    inference(superposition,[status(thm)],[c_1847,c_1853])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(k4_tarski(sK9,sK10),sK8)
    | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1850,plain,
    ( r2_hidden(k4_tarski(sK9,sK10),sK8) = iProver_top
    | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2796,plain,
    ( r2_hidden(k4_tarski(sK9,sK10),sK8) = iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2517,c_1850])).

cnf(c_3404,plain,
    ( r2_hidden(k4_tarski(sK9,sK10),X0) = iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top
    | r1_tarski(sK8,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2796,c_1870])).

cnf(c_3970,plain,
    ( r2_hidden(sK10,X0) = iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top
    | r1_tarski(sK8,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3404,c_1868])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK10,sK6)
    | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1851,plain,
    ( r2_hidden(sK10,sK6) = iProver_top
    | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2797,plain,
    ( r2_hidden(sK10,sK6) = iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2517,c_1851])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1860,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4547,plain,
    ( r2_hidden(sK10,X0) != iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,X0)) = iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2796,c_1860])).

cnf(c_5271,plain,
    ( r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,X0)) = iProver_top
    | r2_hidden(sK10,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4547,c_3338])).

cnf(c_5272,plain,
    ( r2_hidden(sK10,X0) != iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,X0)) = iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5271])).

cnf(c_5281,plain,
    ( r2_hidden(sK10,sK6) != iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_5272])).

cnf(c_5283,plain,
    ( r2_hidden(sK10,sK6) != iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5281])).

cnf(c_5298,plain,
    ( r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3970,c_2797,c_5283])).

cnf(c_2799,plain,
    ( m1_subset_1(X0,sK7) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k4_tarski(sK9,X0),sK8) != iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2517,c_1852])).

cnf(c_3377,plain,
    ( m1_subset_1(sK4(sK9,X0,sK8),sK7) != iProver_top
    | r2_hidden(sK4(sK9,X0,sK8),sK6) != iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,X0)) != iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,sK6)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1855,c_2799])).

cnf(c_3532,plain,
    ( r2_hidden(sK9,k10_relat_1(sK8,sK6)) != iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,X0)) != iProver_top
    | r2_hidden(sK4(sK9,X0,sK8),sK6) != iProver_top
    | m1_subset_1(sK4(sK9,X0,sK8),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3377,c_3338])).

cnf(c_3533,plain,
    ( m1_subset_1(sK4(sK9,X0,sK8),sK7) != iProver_top
    | r2_hidden(sK4(sK9,X0,sK8),sK6) != iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,X0)) != iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3532])).

cnf(c_12502,plain,
    ( r2_hidden(sK4(sK9,X0,sK8),sK6) != iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,X0)) != iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12493,c_3533])).

cnf(c_12684,plain,
    ( r2_hidden(sK4(sK9,X0,sK8),sK6) != iProver_top
    | r2_hidden(sK9,k10_relat_1(sK8,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12504,c_2797,c_5283,c_12502])).

cnf(c_12688,plain,
    ( r2_hidden(sK9,k10_relat_1(sK8,sK6)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1856,c_12684])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12688,c_5298,c_3338])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:05:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.45/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.45/0.99  
% 3.45/0.99  ------  iProver source info
% 3.45/0.99  
% 3.45/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.45/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.45/0.99  git: non_committed_changes: false
% 3.45/0.99  git: last_make_outside_of_git: false
% 3.45/0.99  
% 3.45/0.99  ------ 
% 3.45/0.99  
% 3.45/0.99  ------ Input Options
% 3.45/0.99  
% 3.45/0.99  --out_options                           all
% 3.45/0.99  --tptp_safe_out                         true
% 3.45/0.99  --problem_path                          ""
% 3.45/0.99  --include_path                          ""
% 3.45/0.99  --clausifier                            res/vclausify_rel
% 3.45/0.99  --clausifier_options                    ""
% 3.45/0.99  --stdin                                 false
% 3.45/0.99  --stats_out                             all
% 3.45/0.99  
% 3.45/0.99  ------ General Options
% 3.45/0.99  
% 3.45/0.99  --fof                                   false
% 3.45/0.99  --time_out_real                         305.
% 3.45/0.99  --time_out_virtual                      -1.
% 3.45/0.99  --symbol_type_check                     false
% 3.45/0.99  --clausify_out                          false
% 3.45/0.99  --sig_cnt_out                           false
% 3.45/0.99  --trig_cnt_out                          false
% 3.45/0.99  --trig_cnt_out_tolerance                1.
% 3.45/0.99  --trig_cnt_out_sk_spl                   false
% 3.45/0.99  --abstr_cl_out                          false
% 3.45/0.99  
% 3.45/0.99  ------ Global Options
% 3.45/0.99  
% 3.45/0.99  --schedule                              default
% 3.45/0.99  --add_important_lit                     false
% 3.45/0.99  --prop_solver_per_cl                    1000
% 3.45/0.99  --min_unsat_core                        false
% 3.45/0.99  --soft_assumptions                      false
% 3.45/0.99  --soft_lemma_size                       3
% 3.45/0.99  --prop_impl_unit_size                   0
% 3.45/0.99  --prop_impl_unit                        []
% 3.45/0.99  --share_sel_clauses                     true
% 3.45/0.99  --reset_solvers                         false
% 3.45/0.99  --bc_imp_inh                            [conj_cone]
% 3.45/0.99  --conj_cone_tolerance                   3.
% 3.45/0.99  --extra_neg_conj                        none
% 3.45/0.99  --large_theory_mode                     true
% 3.45/0.99  --prolific_symb_bound                   200
% 3.45/0.99  --lt_threshold                          2000
% 3.45/0.99  --clause_weak_htbl                      true
% 3.45/0.99  --gc_record_bc_elim                     false
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing Options
% 3.45/0.99  
% 3.45/0.99  --preprocessing_flag                    true
% 3.45/0.99  --time_out_prep_mult                    0.1
% 3.45/0.99  --splitting_mode                        input
% 3.45/0.99  --splitting_grd                         true
% 3.45/0.99  --splitting_cvd                         false
% 3.45/0.99  --splitting_cvd_svl                     false
% 3.45/0.99  --splitting_nvd                         32
% 3.45/0.99  --sub_typing                            true
% 3.45/0.99  --prep_gs_sim                           true
% 3.45/0.99  --prep_unflatten                        true
% 3.45/0.99  --prep_res_sim                          true
% 3.45/0.99  --prep_upred                            true
% 3.45/0.99  --prep_sem_filter                       exhaustive
% 3.45/0.99  --prep_sem_filter_out                   false
% 3.45/0.99  --pred_elim                             true
% 3.45/0.99  --res_sim_input                         true
% 3.45/0.99  --eq_ax_congr_red                       true
% 3.45/0.99  --pure_diseq_elim                       true
% 3.45/0.99  --brand_transform                       false
% 3.45/0.99  --non_eq_to_eq                          false
% 3.45/0.99  --prep_def_merge                        true
% 3.45/0.99  --prep_def_merge_prop_impl              false
% 3.45/0.99  --prep_def_merge_mbd                    true
% 3.45/0.99  --prep_def_merge_tr_red                 false
% 3.45/0.99  --prep_def_merge_tr_cl                  false
% 3.45/0.99  --smt_preprocessing                     true
% 3.45/0.99  --smt_ac_axioms                         fast
% 3.45/0.99  --preprocessed_out                      false
% 3.45/0.99  --preprocessed_stats                    false
% 3.45/0.99  
% 3.45/0.99  ------ Abstraction refinement Options
% 3.45/0.99  
% 3.45/0.99  --abstr_ref                             []
% 3.45/0.99  --abstr_ref_prep                        false
% 3.45/0.99  --abstr_ref_until_sat                   false
% 3.45/0.99  --abstr_ref_sig_restrict                funpre
% 3.45/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/0.99  --abstr_ref_under                       []
% 3.45/0.99  
% 3.45/0.99  ------ SAT Options
% 3.45/0.99  
% 3.45/0.99  --sat_mode                              false
% 3.45/0.99  --sat_fm_restart_options                ""
% 3.45/0.99  --sat_gr_def                            false
% 3.45/0.99  --sat_epr_types                         true
% 3.45/0.99  --sat_non_cyclic_types                  false
% 3.45/0.99  --sat_finite_models                     false
% 3.45/0.99  --sat_fm_lemmas                         false
% 3.45/0.99  --sat_fm_prep                           false
% 3.45/0.99  --sat_fm_uc_incr                        true
% 3.45/0.99  --sat_out_model                         small
% 3.45/0.99  --sat_out_clauses                       false
% 3.45/0.99  
% 3.45/0.99  ------ QBF Options
% 3.45/0.99  
% 3.45/0.99  --qbf_mode                              false
% 3.45/0.99  --qbf_elim_univ                         false
% 3.45/0.99  --qbf_dom_inst                          none
% 3.45/0.99  --qbf_dom_pre_inst                      false
% 3.45/0.99  --qbf_sk_in                             false
% 3.45/0.99  --qbf_pred_elim                         true
% 3.45/0.99  --qbf_split                             512
% 3.45/0.99  
% 3.45/0.99  ------ BMC1 Options
% 3.45/0.99  
% 3.45/0.99  --bmc1_incremental                      false
% 3.45/0.99  --bmc1_axioms                           reachable_all
% 3.45/0.99  --bmc1_min_bound                        0
% 3.45/0.99  --bmc1_max_bound                        -1
% 3.45/0.99  --bmc1_max_bound_default                -1
% 3.45/0.99  --bmc1_symbol_reachability              true
% 3.45/0.99  --bmc1_property_lemmas                  false
% 3.45/0.99  --bmc1_k_induction                      false
% 3.45/0.99  --bmc1_non_equiv_states                 false
% 3.45/0.99  --bmc1_deadlock                         false
% 3.45/0.99  --bmc1_ucm                              false
% 3.45/0.99  --bmc1_add_unsat_core                   none
% 3.45/0.99  --bmc1_unsat_core_children              false
% 3.45/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/0.99  --bmc1_out_stat                         full
% 3.45/0.99  --bmc1_ground_init                      false
% 3.45/0.99  --bmc1_pre_inst_next_state              false
% 3.45/0.99  --bmc1_pre_inst_state                   false
% 3.45/0.99  --bmc1_pre_inst_reach_state             false
% 3.45/0.99  --bmc1_out_unsat_core                   false
% 3.45/0.99  --bmc1_aig_witness_out                  false
% 3.45/0.99  --bmc1_verbose                          false
% 3.45/0.99  --bmc1_dump_clauses_tptp                false
% 3.45/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.45/0.99  --bmc1_dump_file                        -
% 3.45/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.45/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.45/0.99  --bmc1_ucm_extend_mode                  1
% 3.45/0.99  --bmc1_ucm_init_mode                    2
% 3.45/0.99  --bmc1_ucm_cone_mode                    none
% 3.45/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.45/0.99  --bmc1_ucm_relax_model                  4
% 3.45/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.45/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/0.99  --bmc1_ucm_layered_model                none
% 3.45/0.99  --bmc1_ucm_max_lemma_size               10
% 3.45/0.99  
% 3.45/0.99  ------ AIG Options
% 3.45/0.99  
% 3.45/0.99  --aig_mode                              false
% 3.45/0.99  
% 3.45/0.99  ------ Instantiation Options
% 3.45/0.99  
% 3.45/0.99  --instantiation_flag                    true
% 3.45/0.99  --inst_sos_flag                         true
% 3.45/0.99  --inst_sos_phase                        true
% 3.45/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel_side                     num_symb
% 3.45/0.99  --inst_solver_per_active                1400
% 3.45/0.99  --inst_solver_calls_frac                1.
% 3.45/0.99  --inst_passive_queue_type               priority_queues
% 3.45/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/0.99  --inst_passive_queues_freq              [25;2]
% 3.45/0.99  --inst_dismatching                      true
% 3.45/0.99  --inst_eager_unprocessed_to_passive     true
% 3.45/0.99  --inst_prop_sim_given                   true
% 3.45/0.99  --inst_prop_sim_new                     false
% 3.45/0.99  --inst_subs_new                         false
% 3.45/0.99  --inst_eq_res_simp                      false
% 3.45/0.99  --inst_subs_given                       false
% 3.45/0.99  --inst_orphan_elimination               true
% 3.45/0.99  --inst_learning_loop_flag               true
% 3.45/0.99  --inst_learning_start                   3000
% 3.45/0.99  --inst_learning_factor                  2
% 3.45/0.99  --inst_start_prop_sim_after_learn       3
% 3.45/0.99  --inst_sel_renew                        solver
% 3.45/0.99  --inst_lit_activity_flag                true
% 3.45/0.99  --inst_restr_to_given                   false
% 3.45/0.99  --inst_activity_threshold               500
% 3.45/0.99  --inst_out_proof                        true
% 3.45/0.99  
% 3.45/0.99  ------ Resolution Options
% 3.45/0.99  
% 3.45/0.99  --resolution_flag                       true
% 3.45/0.99  --res_lit_sel                           adaptive
% 3.45/0.99  --res_lit_sel_side                      none
% 3.45/0.99  --res_ordering                          kbo
% 3.45/0.99  --res_to_prop_solver                    active
% 3.45/0.99  --res_prop_simpl_new                    false
% 3.45/0.99  --res_prop_simpl_given                  true
% 3.45/0.99  --res_passive_queue_type                priority_queues
% 3.45/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/0.99  --res_passive_queues_freq               [15;5]
% 3.45/0.99  --res_forward_subs                      full
% 3.45/0.99  --res_backward_subs                     full
% 3.45/0.99  --res_forward_subs_resolution           true
% 3.45/0.99  --res_backward_subs_resolution          true
% 3.45/0.99  --res_orphan_elimination                true
% 3.45/0.99  --res_time_limit                        2.
% 3.45/0.99  --res_out_proof                         true
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Options
% 3.45/0.99  
% 3.45/0.99  --superposition_flag                    true
% 3.45/0.99  --sup_passive_queue_type                priority_queues
% 3.45/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.45/0.99  --demod_completeness_check              fast
% 3.45/0.99  --demod_use_ground                      true
% 3.45/0.99  --sup_to_prop_solver                    passive
% 3.45/0.99  --sup_prop_simpl_new                    true
% 3.45/0.99  --sup_prop_simpl_given                  true
% 3.45/0.99  --sup_fun_splitting                     true
% 3.45/0.99  --sup_smt_interval                      50000
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Simplification Setup
% 3.45/0.99  
% 3.45/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.45/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.45/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.45/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.45/0.99  --sup_immed_triv                        [TrivRules]
% 3.45/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.99  --sup_immed_bw_main                     []
% 3.45/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.45/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.99  --sup_input_bw                          []
% 3.45/0.99  
% 3.45/0.99  ------ Combination Options
% 3.45/0.99  
% 3.45/0.99  --comb_res_mult                         3
% 3.45/0.99  --comb_sup_mult                         2
% 3.45/0.99  --comb_inst_mult                        10
% 3.45/0.99  
% 3.45/0.99  ------ Debug Options
% 3.45/0.99  
% 3.45/0.99  --dbg_backtrace                         false
% 3.45/0.99  --dbg_dump_prop_clauses                 false
% 3.45/0.99  --dbg_dump_prop_clauses_file            -
% 3.45/0.99  --dbg_out_stat                          false
% 3.45/0.99  ------ Parsing...
% 3.45/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.45/0.99  ------ Proving...
% 3.45/0.99  ------ Problem Properties 
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  clauses                                 27
% 3.45/0.99  conjectures                             6
% 3.45/0.99  EPR                                     4
% 3.45/0.99  Horn                                    21
% 3.45/0.99  unary                                   3
% 3.45/0.99  binary                                  11
% 3.45/0.99  lits                                    70
% 3.45/0.99  lits eq                                 4
% 3.45/0.99  fd_pure                                 0
% 3.45/0.99  fd_pseudo                               0
% 3.45/0.99  fd_cond                                 0
% 3.45/0.99  fd_pseudo_cond                          3
% 3.45/0.99  AC symbols                              0
% 3.45/0.99  
% 3.45/0.99  ------ Schedule dynamic 5 is on 
% 3.45/0.99  
% 3.45/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  ------ 
% 3.45/0.99  Current options:
% 3.45/0.99  ------ 
% 3.45/0.99  
% 3.45/0.99  ------ Input Options
% 3.45/0.99  
% 3.45/0.99  --out_options                           all
% 3.45/0.99  --tptp_safe_out                         true
% 3.45/0.99  --problem_path                          ""
% 3.45/0.99  --include_path                          ""
% 3.45/0.99  --clausifier                            res/vclausify_rel
% 3.45/0.99  --clausifier_options                    ""
% 3.45/0.99  --stdin                                 false
% 3.45/0.99  --stats_out                             all
% 3.45/0.99  
% 3.45/0.99  ------ General Options
% 3.45/0.99  
% 3.45/0.99  --fof                                   false
% 3.45/0.99  --time_out_real                         305.
% 3.45/0.99  --time_out_virtual                      -1.
% 3.45/0.99  --symbol_type_check                     false
% 3.45/0.99  --clausify_out                          false
% 3.45/0.99  --sig_cnt_out                           false
% 3.45/0.99  --trig_cnt_out                          false
% 3.45/0.99  --trig_cnt_out_tolerance                1.
% 3.45/0.99  --trig_cnt_out_sk_spl                   false
% 3.45/0.99  --abstr_cl_out                          false
% 3.45/0.99  
% 3.45/0.99  ------ Global Options
% 3.45/0.99  
% 3.45/0.99  --schedule                              default
% 3.45/0.99  --add_important_lit                     false
% 3.45/0.99  --prop_solver_per_cl                    1000
% 3.45/0.99  --min_unsat_core                        false
% 3.45/0.99  --soft_assumptions                      false
% 3.45/0.99  --soft_lemma_size                       3
% 3.45/0.99  --prop_impl_unit_size                   0
% 3.45/0.99  --prop_impl_unit                        []
% 3.45/0.99  --share_sel_clauses                     true
% 3.45/0.99  --reset_solvers                         false
% 3.45/0.99  --bc_imp_inh                            [conj_cone]
% 3.45/0.99  --conj_cone_tolerance                   3.
% 3.45/0.99  --extra_neg_conj                        none
% 3.45/0.99  --large_theory_mode                     true
% 3.45/0.99  --prolific_symb_bound                   200
% 3.45/0.99  --lt_threshold                          2000
% 3.45/0.99  --clause_weak_htbl                      true
% 3.45/0.99  --gc_record_bc_elim                     false
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing Options
% 3.45/0.99  
% 3.45/0.99  --preprocessing_flag                    true
% 3.45/0.99  --time_out_prep_mult                    0.1
% 3.45/0.99  --splitting_mode                        input
% 3.45/0.99  --splitting_grd                         true
% 3.45/0.99  --splitting_cvd                         false
% 3.45/0.99  --splitting_cvd_svl                     false
% 3.45/0.99  --splitting_nvd                         32
% 3.45/0.99  --sub_typing                            true
% 3.45/0.99  --prep_gs_sim                           true
% 3.45/0.99  --prep_unflatten                        true
% 3.45/0.99  --prep_res_sim                          true
% 3.45/0.99  --prep_upred                            true
% 3.45/0.99  --prep_sem_filter                       exhaustive
% 3.45/0.99  --prep_sem_filter_out                   false
% 3.45/0.99  --pred_elim                             true
% 3.45/0.99  --res_sim_input                         true
% 3.45/0.99  --eq_ax_congr_red                       true
% 3.45/0.99  --pure_diseq_elim                       true
% 3.45/0.99  --brand_transform                       false
% 3.45/0.99  --non_eq_to_eq                          false
% 3.45/0.99  --prep_def_merge                        true
% 3.45/0.99  --prep_def_merge_prop_impl              false
% 3.45/0.99  --prep_def_merge_mbd                    true
% 3.45/0.99  --prep_def_merge_tr_red                 false
% 3.45/0.99  --prep_def_merge_tr_cl                  false
% 3.45/0.99  --smt_preprocessing                     true
% 3.45/0.99  --smt_ac_axioms                         fast
% 3.45/0.99  --preprocessed_out                      false
% 3.45/0.99  --preprocessed_stats                    false
% 3.45/0.99  
% 3.45/0.99  ------ Abstraction refinement Options
% 3.45/0.99  
% 3.45/0.99  --abstr_ref                             []
% 3.45/0.99  --abstr_ref_prep                        false
% 3.45/0.99  --abstr_ref_until_sat                   false
% 3.45/0.99  --abstr_ref_sig_restrict                funpre
% 3.45/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/0.99  --abstr_ref_under                       []
% 3.45/0.99  
% 3.45/0.99  ------ SAT Options
% 3.45/0.99  
% 3.45/0.99  --sat_mode                              false
% 3.45/0.99  --sat_fm_restart_options                ""
% 3.45/0.99  --sat_gr_def                            false
% 3.45/0.99  --sat_epr_types                         true
% 3.45/0.99  --sat_non_cyclic_types                  false
% 3.45/0.99  --sat_finite_models                     false
% 3.45/0.99  --sat_fm_lemmas                         false
% 3.45/0.99  --sat_fm_prep                           false
% 3.45/0.99  --sat_fm_uc_incr                        true
% 3.45/0.99  --sat_out_model                         small
% 3.45/0.99  --sat_out_clauses                       false
% 3.45/0.99  
% 3.45/0.99  ------ QBF Options
% 3.45/0.99  
% 3.45/0.99  --qbf_mode                              false
% 3.45/0.99  --qbf_elim_univ                         false
% 3.45/0.99  --qbf_dom_inst                          none
% 3.45/0.99  --qbf_dom_pre_inst                      false
% 3.45/0.99  --qbf_sk_in                             false
% 3.45/0.99  --qbf_pred_elim                         true
% 3.45/0.99  --qbf_split                             512
% 3.45/0.99  
% 3.45/0.99  ------ BMC1 Options
% 3.45/0.99  
% 3.45/0.99  --bmc1_incremental                      false
% 3.45/0.99  --bmc1_axioms                           reachable_all
% 3.45/0.99  --bmc1_min_bound                        0
% 3.45/0.99  --bmc1_max_bound                        -1
% 3.45/0.99  --bmc1_max_bound_default                -1
% 3.45/0.99  --bmc1_symbol_reachability              true
% 3.45/0.99  --bmc1_property_lemmas                  false
% 3.45/0.99  --bmc1_k_induction                      false
% 3.45/0.99  --bmc1_non_equiv_states                 false
% 3.45/0.99  --bmc1_deadlock                         false
% 3.45/0.99  --bmc1_ucm                              false
% 3.45/0.99  --bmc1_add_unsat_core                   none
% 3.45/0.99  --bmc1_unsat_core_children              false
% 3.45/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/0.99  --bmc1_out_stat                         full
% 3.45/0.99  --bmc1_ground_init                      false
% 3.45/0.99  --bmc1_pre_inst_next_state              false
% 3.45/0.99  --bmc1_pre_inst_state                   false
% 3.45/0.99  --bmc1_pre_inst_reach_state             false
% 3.45/0.99  --bmc1_out_unsat_core                   false
% 3.45/0.99  --bmc1_aig_witness_out                  false
% 3.45/0.99  --bmc1_verbose                          false
% 3.45/0.99  --bmc1_dump_clauses_tptp                false
% 3.45/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.45/0.99  --bmc1_dump_file                        -
% 3.45/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.45/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.45/0.99  --bmc1_ucm_extend_mode                  1
% 3.45/0.99  --bmc1_ucm_init_mode                    2
% 3.45/0.99  --bmc1_ucm_cone_mode                    none
% 3.45/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.45/0.99  --bmc1_ucm_relax_model                  4
% 3.45/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.45/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/0.99  --bmc1_ucm_layered_model                none
% 3.45/0.99  --bmc1_ucm_max_lemma_size               10
% 3.45/0.99  
% 3.45/0.99  ------ AIG Options
% 3.45/0.99  
% 3.45/0.99  --aig_mode                              false
% 3.45/0.99  
% 3.45/0.99  ------ Instantiation Options
% 3.45/0.99  
% 3.45/0.99  --instantiation_flag                    true
% 3.45/0.99  --inst_sos_flag                         true
% 3.45/0.99  --inst_sos_phase                        true
% 3.45/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel_side                     none
% 3.45/0.99  --inst_solver_per_active                1400
% 3.45/0.99  --inst_solver_calls_frac                1.
% 3.45/0.99  --inst_passive_queue_type               priority_queues
% 3.45/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/0.99  --inst_passive_queues_freq              [25;2]
% 3.45/0.99  --inst_dismatching                      true
% 3.45/0.99  --inst_eager_unprocessed_to_passive     true
% 3.45/0.99  --inst_prop_sim_given                   true
% 3.45/0.99  --inst_prop_sim_new                     false
% 3.45/0.99  --inst_subs_new                         false
% 3.45/0.99  --inst_eq_res_simp                      false
% 3.45/0.99  --inst_subs_given                       false
% 3.45/0.99  --inst_orphan_elimination               true
% 3.45/0.99  --inst_learning_loop_flag               true
% 3.45/0.99  --inst_learning_start                   3000
% 3.45/0.99  --inst_learning_factor                  2
% 3.45/0.99  --inst_start_prop_sim_after_learn       3
% 3.45/0.99  --inst_sel_renew                        solver
% 3.45/0.99  --inst_lit_activity_flag                true
% 3.45/0.99  --inst_restr_to_given                   false
% 3.45/0.99  --inst_activity_threshold               500
% 3.45/0.99  --inst_out_proof                        true
% 3.45/0.99  
% 3.45/0.99  ------ Resolution Options
% 3.45/0.99  
% 3.45/0.99  --resolution_flag                       false
% 3.45/0.99  --res_lit_sel                           adaptive
% 3.45/0.99  --res_lit_sel_side                      none
% 3.45/0.99  --res_ordering                          kbo
% 3.45/0.99  --res_to_prop_solver                    active
% 3.45/0.99  --res_prop_simpl_new                    false
% 3.45/0.99  --res_prop_simpl_given                  true
% 3.45/0.99  --res_passive_queue_type                priority_queues
% 3.45/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/0.99  --res_passive_queues_freq               [15;5]
% 3.45/0.99  --res_forward_subs                      full
% 3.45/0.99  --res_backward_subs                     full
% 3.45/0.99  --res_forward_subs_resolution           true
% 3.45/0.99  --res_backward_subs_resolution          true
% 3.45/0.99  --res_orphan_elimination                true
% 3.45/0.99  --res_time_limit                        2.
% 3.45/0.99  --res_out_proof                         true
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Options
% 3.45/0.99  
% 3.45/0.99  --superposition_flag                    true
% 3.45/0.99  --sup_passive_queue_type                priority_queues
% 3.45/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.45/0.99  --demod_completeness_check              fast
% 3.45/0.99  --demod_use_ground                      true
% 3.45/0.99  --sup_to_prop_solver                    passive
% 3.45/0.99  --sup_prop_simpl_new                    true
% 3.45/0.99  --sup_prop_simpl_given                  true
% 3.45/0.99  --sup_fun_splitting                     true
% 3.45/0.99  --sup_smt_interval                      50000
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Simplification Setup
% 3.45/0.99  
% 3.45/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.45/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.45/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.45/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.45/0.99  --sup_immed_triv                        [TrivRules]
% 3.45/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.99  --sup_immed_bw_main                     []
% 3.45/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.45/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.99  --sup_input_bw                          []
% 3.45/0.99  
% 3.45/0.99  ------ Combination Options
% 3.45/0.99  
% 3.45/0.99  --comb_res_mult                         3
% 3.45/0.99  --comb_sup_mult                         2
% 3.45/0.99  --comb_inst_mult                        10
% 3.45/0.99  
% 3.45/0.99  ------ Debug Options
% 3.45/0.99  
% 3.45/0.99  --dbg_backtrace                         false
% 3.45/0.99  --dbg_dump_prop_clauses                 false
% 3.45/0.99  --dbg_dump_prop_clauses_file            -
% 3.45/0.99  --dbg_out_stat                          false
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  ------ Proving...
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  % SZS status Theorem for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  fof(f8,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f17,plain,(
% 3.45/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.45/0.99    inference(ennf_transformation,[],[f8])).
% 3.45/0.99  
% 3.45/0.99  fof(f33,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.45/0.99    inference(nnf_transformation,[],[f17])).
% 3.45/0.99  
% 3.45/0.99  fof(f34,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.45/0.99    inference(rectify,[],[f33])).
% 3.45/0.99  
% 3.45/0.99  fof(f35,plain,(
% 3.45/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f36,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 3.45/0.99  
% 3.45/0.99  fof(f63,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f36])).
% 3.45/0.99  
% 3.45/0.99  fof(f10,conjecture,(
% 3.45/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f11,negated_conjecture,(
% 3.45/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 3.45/0.99    inference(negated_conjecture,[],[f10])).
% 3.45/0.99  
% 3.45/0.99  fof(f12,plain,(
% 3.45/0.99    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)))))),
% 3.45/0.99    inference(pure_predicate_removal,[],[f11])).
% 3.45/0.99  
% 3.45/0.99  fof(f19,plain,(
% 3.45/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.45/0.99    inference(ennf_transformation,[],[f12])).
% 3.45/0.99  
% 3.45/0.99  fof(f37,plain,(
% 3.45/0.99    ? [X0,X1,X2,X3] : (? [X4] : (((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.45/0.99    inference(nnf_transformation,[],[f19])).
% 3.45/0.99  
% 3.45/0.99  fof(f38,plain,(
% 3.45/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.45/0.99    inference(flattening,[],[f37])).
% 3.45/0.99  
% 3.45/0.99  fof(f39,plain,(
% 3.45/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.45/0.99    inference(rectify,[],[f38])).
% 3.45/0.99  
% 3.45/0.99  fof(f42,plain,(
% 3.45/0.99    ( ! [X4,X2,X3,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK10,X1) & r2_hidden(k4_tarski(X4,sK10),X3) & m1_subset_1(sK10,X2))) )),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f41,plain,(
% 3.45/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) => ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(sK9,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(sK9,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(sK9,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(sK9,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(sK9,X0))) )),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f40,plain,(
% 3.45/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (? [X4] : ((! [X5] : (~r2_hidden(X5,sK6) | ~r2_hidden(k4_tarski(X4,X5),sK8) | ~m1_subset_1(X5,sK7)) | ~r2_hidden(X4,k8_relset_1(sK5,sK7,sK8,sK6))) & (? [X6] : (r2_hidden(X6,sK6) & r2_hidden(k4_tarski(X4,X6),sK8) & m1_subset_1(X6,sK7)) | r2_hidden(X4,k8_relset_1(sK5,sK7,sK8,sK6))) & m1_subset_1(X4,sK5)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK7))))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f43,plain,(
% 3.45/0.99    ((! [X5] : (~r2_hidden(X5,sK6) | ~r2_hidden(k4_tarski(sK9,X5),sK8) | ~m1_subset_1(X5,sK7)) | ~r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6))) & ((r2_hidden(sK10,sK6) & r2_hidden(k4_tarski(sK9,sK10),sK8) & m1_subset_1(sK10,sK7)) | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6))) & m1_subset_1(sK9,sK5)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK7)))),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9,sK10])],[f39,f42,f41,f40])).
% 3.45/0.99  
% 3.45/0.99  fof(f66,plain,(
% 3.45/0.99    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK7)))),
% 3.45/0.99    inference(cnf_transformation,[],[f43])).
% 3.45/0.99  
% 3.45/0.99  fof(f4,axiom,(
% 3.45/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f26,plain,(
% 3.45/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.45/0.99    inference(nnf_transformation,[],[f4])).
% 3.45/0.99  
% 3.45/0.99  fof(f51,plain,(
% 3.45/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f26])).
% 3.45/0.99  
% 3.45/0.99  fof(f62,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f36])).
% 3.45/0.99  
% 3.45/0.99  fof(f1,axiom,(
% 3.45/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f13,plain,(
% 3.45/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.45/0.99    inference(ennf_transformation,[],[f1])).
% 3.45/0.99  
% 3.45/0.99  fof(f20,plain,(
% 3.45/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.45/0.99    inference(nnf_transformation,[],[f13])).
% 3.45/0.99  
% 3.45/0.99  fof(f21,plain,(
% 3.45/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.45/0.99    inference(rectify,[],[f20])).
% 3.45/0.99  
% 3.45/0.99  fof(f22,plain,(
% 3.45/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f23,plain,(
% 3.45/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 3.45/0.99  
% 3.45/0.99  fof(f44,plain,(
% 3.45/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f23])).
% 3.45/0.99  
% 3.45/0.99  fof(f2,axiom,(
% 3.45/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f24,plain,(
% 3.45/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.45/0.99    inference(nnf_transformation,[],[f2])).
% 3.45/0.99  
% 3.45/0.99  fof(f25,plain,(
% 3.45/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.45/0.99    inference(flattening,[],[f24])).
% 3.45/0.99  
% 3.45/0.99  fof(f48,plain,(
% 3.45/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f25])).
% 3.45/0.99  
% 3.45/0.99  fof(f7,axiom,(
% 3.45/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f60,plain,(
% 3.45/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f7])).
% 3.45/0.99  
% 3.45/0.99  fof(f5,axiom,(
% 3.45/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f15,plain,(
% 3.45/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.45/0.99    inference(ennf_transformation,[],[f5])).
% 3.45/0.99  
% 3.45/0.99  fof(f53,plain,(
% 3.45/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f15])).
% 3.45/0.99  
% 3.45/0.99  fof(f52,plain,(
% 3.45/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f26])).
% 3.45/0.99  
% 3.45/0.99  fof(f3,axiom,(
% 3.45/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f14,plain,(
% 3.45/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.45/0.99    inference(ennf_transformation,[],[f3])).
% 3.45/0.99  
% 3.45/0.99  fof(f50,plain,(
% 3.45/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f14])).
% 3.45/0.99  
% 3.45/0.99  fof(f68,plain,(
% 3.45/0.99    m1_subset_1(sK10,sK7) | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6))),
% 3.45/0.99    inference(cnf_transformation,[],[f43])).
% 3.45/0.99  
% 3.45/0.99  fof(f71,plain,(
% 3.45/0.99    ( ! [X5] : (~r2_hidden(X5,sK6) | ~r2_hidden(k4_tarski(sK9,X5),sK8) | ~m1_subset_1(X5,sK7) | ~r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f43])).
% 3.45/0.99  
% 3.45/0.99  fof(f9,axiom,(
% 3.45/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f18,plain,(
% 3.45/0.99    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(ennf_transformation,[],[f9])).
% 3.45/0.99  
% 3.45/0.99  fof(f65,plain,(
% 3.45/0.99    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f18])).
% 3.45/0.99  
% 3.45/0.99  fof(f69,plain,(
% 3.45/0.99    r2_hidden(k4_tarski(sK9,sK10),sK8) | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6))),
% 3.45/0.99    inference(cnf_transformation,[],[f43])).
% 3.45/0.99  
% 3.45/0.99  fof(f70,plain,(
% 3.45/0.99    r2_hidden(sK10,sK6) | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6))),
% 3.45/0.99    inference(cnf_transformation,[],[f43])).
% 3.45/0.99  
% 3.45/0.99  fof(f6,axiom,(
% 3.45/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f16,plain,(
% 3.45/0.99    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 3.45/0.99    inference(ennf_transformation,[],[f6])).
% 3.45/0.99  
% 3.45/0.99  fof(f27,plain,(
% 3.45/0.99    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.45/0.99    inference(nnf_transformation,[],[f16])).
% 3.45/0.99  
% 3.45/0.99  fof(f28,plain,(
% 3.45/0.99    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.45/0.99    inference(rectify,[],[f27])).
% 3.45/0.99  
% 3.45/0.99  fof(f31,plain,(
% 3.45/0.99    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f30,plain,(
% 3.45/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0)))) )),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f29,plain,(
% 3.45/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f32,plain,(
% 3.45/0.99    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f31,f30,f29])).
% 3.45/0.99  
% 3.45/0.99  fof(f56,plain,(
% 3.45/0.99    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f32])).
% 3.45/0.99  
% 3.45/0.99  fof(f72,plain,(
% 3.45/0.99    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k10_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~v1_relat_1(X0)) )),
% 3.45/0.99    inference(equality_resolution,[],[f56])).
% 3.45/0.99  
% 3.45/0.99  cnf(c_18,plain,
% 3.45/0.99      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.45/0.99      | r2_hidden(sK4(X0,X2,X1),X2)
% 3.45/0.99      | ~ v1_relat_1(X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1856,plain,
% 3.45/0.99      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 3.45/0.99      | r2_hidden(sK4(X0,X2,X1),X2) = iProver_top
% 3.45/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_27,negated_conjecture,
% 3.45/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK7))) ),
% 3.45/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1847,plain,
% 3.45/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK7))) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_8,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1864,plain,
% 3.45/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.45/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2600,plain,
% 3.45/0.99      ( r1_tarski(sK8,k2_zfmisc_1(sK5,sK7)) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1847,c_1864]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_19,plain,
% 3.45/0.99      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.45/0.99      | r2_hidden(k4_tarski(X0,sK4(X0,X2,X1)),X1)
% 3.45/0.99      | ~ v1_relat_1(X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1855,plain,
% 3.45/0.99      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 3.45/0.99      | r2_hidden(k4_tarski(X0,sK4(X0,X2,X1)),X1) = iProver_top
% 3.45/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2,plain,
% 3.45/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.45/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1870,plain,
% 3.45/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.45/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.45/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3402,plain,
% 3.45/0.99      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 3.45/0.99      | r2_hidden(k4_tarski(X0,sK4(X0,X2,X1)),X3) = iProver_top
% 3.45/0.99      | r1_tarski(X1,X3) != iProver_top
% 3.45/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1855,c_1870]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4,plain,
% 3.45/0.99      ( r2_hidden(X0,X1)
% 3.45/0.99      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1868,plain,
% 3.45/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.45/0.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_6497,plain,
% 3.45/0.99      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 3.45/0.99      | r2_hidden(sK4(X0,X2,X1),X3) = iProver_top
% 3.45/0.99      | r1_tarski(X1,k2_zfmisc_1(X4,X3)) != iProver_top
% 3.45/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_3402,c_1868]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_12423,plain,
% 3.45/0.99      ( r2_hidden(X0,k10_relat_1(sK8,X1)) != iProver_top
% 3.45/0.99      | r2_hidden(sK4(X0,X1,sK8),sK7) = iProver_top
% 3.45/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_2600,c_6497]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_16,plain,
% 3.45/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1857,plain,
% 3.45/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_9,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.45/0.99      | ~ v1_relat_1(X1)
% 3.45/0.99      | v1_relat_1(X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_7,plain,
% 3.45/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_224,plain,
% 3.45/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.45/0.99      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_225,plain,
% 3.45/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.45/0.99      inference(renaming,[status(thm)],[c_224]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_276,plain,
% 3.45/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.45/0.99      inference(bin_hyper_res,[status(thm)],[c_9,c_225]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1846,plain,
% 3.45/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.45/0.99      | v1_relat_1(X1) != iProver_top
% 3.45/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_276]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3334,plain,
% 3.45/0.99      ( v1_relat_1(k2_zfmisc_1(sK5,sK7)) != iProver_top
% 3.45/0.99      | v1_relat_1(sK8) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_2600,c_1846]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3338,plain,
% 3.45/0.99      ( v1_relat_1(sK8) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1857,c_3334]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_12485,plain,
% 3.45/0.99      ( r2_hidden(sK4(X0,X1,sK8),sK7) = iProver_top
% 3.45/0.99      | r2_hidden(X0,k10_relat_1(sK8,X1)) != iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_12423,c_3338]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_12486,plain,
% 3.45/0.99      ( r2_hidden(X0,k10_relat_1(sK8,X1)) != iProver_top
% 3.45/0.99      | r2_hidden(sK4(X0,X1,sK8),sK7) = iProver_top ),
% 3.45/0.99      inference(renaming,[status(thm)],[c_12485]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_6,plain,
% 3.45/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1866,plain,
% 3.45/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.45/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_12493,plain,
% 3.45/0.99      ( m1_subset_1(sK4(X0,X1,sK8),sK7) = iProver_top
% 3.45/0.99      | r2_hidden(X0,k10_relat_1(sK8,X1)) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_12486,c_1866]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_25,negated_conjecture,
% 3.45/0.99      ( m1_subset_1(sK10,sK7)
% 3.45/0.99      | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1849,plain,
% 3.45/0.99      ( m1_subset_1(sK10,sK7) = iProver_top
% 3.45/0.99      | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_22,negated_conjecture,
% 3.45/0.99      ( ~ m1_subset_1(X0,sK7)
% 3.45/0.99      | ~ r2_hidden(X0,sK6)
% 3.45/0.99      | ~ r2_hidden(k4_tarski(sK9,X0),sK8)
% 3.45/0.99      | ~ r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1852,plain,
% 3.45/0.99      ( m1_subset_1(X0,sK7) != iProver_top
% 3.45/0.99      | r2_hidden(X0,sK6) != iProver_top
% 3.45/0.99      | r2_hidden(k4_tarski(sK9,X0),sK8) != iProver_top
% 3.45/0.99      | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2193,plain,
% 3.45/0.99      ( m1_subset_1(X0,sK7) != iProver_top
% 3.45/0.99      | m1_subset_1(sK10,sK7) = iProver_top
% 3.45/0.99      | r2_hidden(X0,sK6) != iProver_top
% 3.45/0.99      | r2_hidden(k4_tarski(sK9,X0),sK8) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1849,c_1852]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3380,plain,
% 3.45/0.99      ( m1_subset_1(sK4(sK9,X0,sK8),sK7) != iProver_top
% 3.45/0.99      | m1_subset_1(sK10,sK7) = iProver_top
% 3.45/0.99      | r2_hidden(sK4(sK9,X0,sK8),sK6) != iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,X0)) != iProver_top
% 3.45/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1855,c_2193]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3513,plain,
% 3.45/0.99      ( r2_hidden(sK9,k10_relat_1(sK8,X0)) != iProver_top
% 3.45/0.99      | r2_hidden(sK4(sK9,X0,sK8),sK6) != iProver_top
% 3.45/0.99      | m1_subset_1(sK10,sK7) = iProver_top
% 3.45/0.99      | m1_subset_1(sK4(sK9,X0,sK8),sK7) != iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_3380,c_3338]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3514,plain,
% 3.45/0.99      ( m1_subset_1(sK4(sK9,X0,sK8),sK7) != iProver_top
% 3.45/0.99      | m1_subset_1(sK10,sK7) = iProver_top
% 3.45/0.99      | r2_hidden(sK4(sK9,X0,sK8),sK6) != iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,X0)) != iProver_top ),
% 3.45/0.99      inference(renaming,[status(thm)],[c_3513]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_12504,plain,
% 3.45/0.99      ( m1_subset_1(sK10,sK7) = iProver_top
% 3.45/0.99      | r2_hidden(sK4(sK9,X0,sK8),sK6) != iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,X0)) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_12493,c_3514]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_21,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.45/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1853,plain,
% 3.45/0.99      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.45/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2517,plain,
% 3.45/0.99      ( k8_relset_1(sK5,sK7,sK8,X0) = k10_relat_1(sK8,X0) ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1847,c_1853]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_24,negated_conjecture,
% 3.45/0.99      ( r2_hidden(k4_tarski(sK9,sK10),sK8)
% 3.45/0.99      | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1850,plain,
% 3.45/0.99      ( r2_hidden(k4_tarski(sK9,sK10),sK8) = iProver_top
% 3.45/0.99      | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2796,plain,
% 3.45/0.99      ( r2_hidden(k4_tarski(sK9,sK10),sK8) = iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top ),
% 3.45/0.99      inference(demodulation,[status(thm)],[c_2517,c_1850]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3404,plain,
% 3.45/0.99      ( r2_hidden(k4_tarski(sK9,sK10),X0) = iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top
% 3.45/0.99      | r1_tarski(sK8,X0) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_2796,c_1870]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3970,plain,
% 3.45/0.99      ( r2_hidden(sK10,X0) = iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top
% 3.45/0.99      | r1_tarski(sK8,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_3404,c_1868]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_23,negated_conjecture,
% 3.45/0.99      ( r2_hidden(sK10,sK6)
% 3.45/0.99      | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1851,plain,
% 3.45/0.99      ( r2_hidden(sK10,sK6) = iProver_top
% 3.45/0.99      | r2_hidden(sK9,k8_relset_1(sK5,sK7,sK8,sK6)) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2797,plain,
% 3.45/0.99      ( r2_hidden(sK10,sK6) = iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top ),
% 3.45/0.99      inference(demodulation,[status(thm)],[c_2517,c_1851]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_13,plain,
% 3.45/0.99      ( ~ r2_hidden(X0,X1)
% 3.45/0.99      | r2_hidden(X2,k10_relat_1(X3,X1))
% 3.45/0.99      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 3.45/0.99      | ~ v1_relat_1(X3) ),
% 3.45/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1860,plain,
% 3.45/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.45/0.99      | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
% 3.45/0.99      | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
% 3.45/0.99      | v1_relat_1(X3) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4547,plain,
% 3.45/0.99      ( r2_hidden(sK10,X0) != iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,X0)) = iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top
% 3.45/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_2796,c_1860]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5271,plain,
% 3.45/0.99      ( r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,X0)) = iProver_top
% 3.45/0.99      | r2_hidden(sK10,X0) != iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_4547,c_3338]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5272,plain,
% 3.45/0.99      ( r2_hidden(sK10,X0) != iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,X0)) = iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top ),
% 3.45/0.99      inference(renaming,[status(thm)],[c_5271]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5281,plain,
% 3.45/0.99      ( r2_hidden(sK10,sK6) != iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top
% 3.45/0.99      | iProver_top != iProver_top ),
% 3.45/0.99      inference(equality_factoring,[status(thm)],[c_5272]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5283,plain,
% 3.45/0.99      ( r2_hidden(sK10,sK6) != iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top ),
% 3.45/0.99      inference(equality_resolution_simp,[status(thm)],[c_5281]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5298,plain,
% 3.45/0.99      ( r2_hidden(sK9,k10_relat_1(sK8,sK6)) = iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_3970,c_2797,c_5283]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2799,plain,
% 3.45/0.99      ( m1_subset_1(X0,sK7) != iProver_top
% 3.45/0.99      | r2_hidden(X0,sK6) != iProver_top
% 3.45/0.99      | r2_hidden(k4_tarski(sK9,X0),sK8) != iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,sK6)) != iProver_top ),
% 3.45/0.99      inference(demodulation,[status(thm)],[c_2517,c_1852]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3377,plain,
% 3.45/0.99      ( m1_subset_1(sK4(sK9,X0,sK8),sK7) != iProver_top
% 3.45/0.99      | r2_hidden(sK4(sK9,X0,sK8),sK6) != iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,X0)) != iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,sK6)) != iProver_top
% 3.45/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1855,c_2799]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3532,plain,
% 3.45/0.99      ( r2_hidden(sK9,k10_relat_1(sK8,sK6)) != iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,X0)) != iProver_top
% 3.45/0.99      | r2_hidden(sK4(sK9,X0,sK8),sK6) != iProver_top
% 3.45/0.99      | m1_subset_1(sK4(sK9,X0,sK8),sK7) != iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_3377,c_3338]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3533,plain,
% 3.45/0.99      ( m1_subset_1(sK4(sK9,X0,sK8),sK7) != iProver_top
% 3.45/0.99      | r2_hidden(sK4(sK9,X0,sK8),sK6) != iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,X0)) != iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,sK6)) != iProver_top ),
% 3.45/0.99      inference(renaming,[status(thm)],[c_3532]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_12502,plain,
% 3.45/0.99      ( r2_hidden(sK4(sK9,X0,sK8),sK6) != iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,X0)) != iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,sK6)) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_12493,c_3533]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_12684,plain,
% 3.45/0.99      ( r2_hidden(sK4(sK9,X0,sK8),sK6) != iProver_top
% 3.45/0.99      | r2_hidden(sK9,k10_relat_1(sK8,X0)) != iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_12504,c_2797,c_5283,c_12502]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_12688,plain,
% 3.45/0.99      ( r2_hidden(sK9,k10_relat_1(sK8,sK6)) != iProver_top
% 3.45/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1856,c_12684]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(contradiction,plain,
% 3.45/0.99      ( $false ),
% 3.45/0.99      inference(minisat,[status(thm)],[c_12688,c_5298,c_3338]) ).
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  ------                               Statistics
% 3.45/0.99  
% 3.45/0.99  ------ General
% 3.45/0.99  
% 3.45/0.99  abstr_ref_over_cycles:                  0
% 3.45/0.99  abstr_ref_under_cycles:                 0
% 3.45/0.99  gc_basic_clause_elim:                   0
% 3.45/0.99  forced_gc_time:                         0
% 3.45/0.99  parsing_time:                           0.011
% 3.45/0.99  unif_index_cands_time:                  0.
% 3.45/0.99  unif_index_add_time:                    0.
% 3.45/0.99  orderings_time:                         0.
% 3.45/0.99  out_proof_time:                         0.011
% 3.45/0.99  total_time:                             0.478
% 3.45/0.99  num_of_symbols:                         52
% 3.45/0.99  num_of_terms:                           20150
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing
% 3.45/0.99  
% 3.45/0.99  num_of_splits:                          0
% 3.45/0.99  num_of_split_atoms:                     0
% 3.45/0.99  num_of_reused_defs:                     0
% 3.45/0.99  num_eq_ax_congr_red:                    57
% 3.45/0.99  num_of_sem_filtered_clauses:            1
% 3.45/0.99  num_of_subtypes:                        0
% 3.45/0.99  monotx_restored_types:                  0
% 3.45/0.99  sat_num_of_epr_types:                   0
% 3.45/0.99  sat_num_of_non_cyclic_types:            0
% 3.45/0.99  sat_guarded_non_collapsed_types:        0
% 3.45/0.99  num_pure_diseq_elim:                    0
% 3.45/0.99  simp_replaced_by:                       0
% 3.45/0.99  res_preprocessed:                       127
% 3.45/0.99  prep_upred:                             0
% 3.45/0.99  prep_unflattend:                        46
% 3.45/0.99  smt_new_axioms:                         0
% 3.45/0.99  pred_elim_cands:                        4
% 3.45/0.99  pred_elim:                              0
% 3.45/0.99  pred_elim_cl:                           0
% 3.45/0.99  pred_elim_cycles:                       4
% 3.45/0.99  merged_defs:                            8
% 3.45/0.99  merged_defs_ncl:                        0
% 3.45/0.99  bin_hyper_res:                          9
% 3.45/0.99  prep_cycles:                            4
% 3.45/0.99  pred_elim_time:                         0.011
% 3.45/0.99  splitting_time:                         0.
% 3.45/0.99  sem_filter_time:                        0.
% 3.45/0.99  monotx_time:                            0.
% 3.45/0.99  subtype_inf_time:                       0.
% 3.45/0.99  
% 3.45/0.99  ------ Problem properties
% 3.45/0.99  
% 3.45/0.99  clauses:                                27
% 3.45/0.99  conjectures:                            6
% 3.45/0.99  epr:                                    4
% 3.45/0.99  horn:                                   21
% 3.45/0.99  ground:                                 5
% 3.45/0.99  unary:                                  3
% 3.45/0.99  binary:                                 11
% 3.45/0.99  lits:                                   70
% 3.45/0.99  lits_eq:                                4
% 3.45/0.99  fd_pure:                                0
% 3.45/0.99  fd_pseudo:                              0
% 3.45/0.99  fd_cond:                                0
% 3.45/0.99  fd_pseudo_cond:                         3
% 3.45/0.99  ac_symbols:                             0
% 3.45/0.99  
% 3.45/0.99  ------ Propositional Solver
% 3.45/0.99  
% 3.45/0.99  prop_solver_calls:                      28
% 3.45/0.99  prop_fast_solver_calls:                 1666
% 3.45/0.99  smt_solver_calls:                       0
% 3.45/0.99  smt_fast_solver_calls:                  0
% 3.45/0.99  prop_num_of_clauses:                    6024
% 3.45/0.99  prop_preprocess_simplified:             13915
% 3.45/0.99  prop_fo_subsumed:                       103
% 3.45/0.99  prop_solver_time:                       0.
% 3.45/0.99  smt_solver_time:                        0.
% 3.45/0.99  smt_fast_solver_time:                   0.
% 3.45/0.99  prop_fast_solver_time:                  0.
% 3.45/0.99  prop_unsat_core_time:                   0.
% 3.45/0.99  
% 3.45/0.99  ------ QBF
% 3.45/0.99  
% 3.45/0.99  qbf_q_res:                              0
% 3.45/0.99  qbf_num_tautologies:                    0
% 3.45/0.99  qbf_prep_cycles:                        0
% 3.45/0.99  
% 3.45/0.99  ------ BMC1
% 3.45/0.99  
% 3.45/0.99  bmc1_current_bound:                     -1
% 3.45/0.99  bmc1_last_solved_bound:                 -1
% 3.45/0.99  bmc1_unsat_core_size:                   -1
% 3.45/0.99  bmc1_unsat_core_parents_size:           -1
% 3.45/0.99  bmc1_merge_next_fun:                    0
% 3.45/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.45/0.99  
% 3.45/0.99  ------ Instantiation
% 3.45/0.99  
% 3.45/0.99  inst_num_of_clauses:                    1363
% 3.45/0.99  inst_num_in_passive:                    97
% 3.45/0.99  inst_num_in_active:                     794
% 3.45/0.99  inst_num_in_unprocessed:                473
% 3.45/0.99  inst_num_of_loops:                      900
% 3.45/0.99  inst_num_of_learning_restarts:          0
% 3.45/0.99  inst_num_moves_active_passive:          104
% 3.45/0.99  inst_lit_activity:                      0
% 3.45/0.99  inst_lit_activity_moves:                0
% 3.45/0.99  inst_num_tautologies:                   0
% 3.45/0.99  inst_num_prop_implied:                  0
% 3.45/0.99  inst_num_existing_simplified:           0
% 3.45/0.99  inst_num_eq_res_simplified:             0
% 3.45/0.99  inst_num_child_elim:                    0
% 3.45/0.99  inst_num_of_dismatching_blockings:      745
% 3.45/0.99  inst_num_of_non_proper_insts:           695
% 3.45/0.99  inst_num_of_duplicates:                 0
% 3.45/0.99  inst_inst_num_from_inst_to_res:         0
% 3.45/0.99  inst_dismatching_checking_time:         0.
% 3.45/0.99  
% 3.45/0.99  ------ Resolution
% 3.45/0.99  
% 3.45/0.99  res_num_of_clauses:                     0
% 3.45/0.99  res_num_in_passive:                     0
% 3.45/0.99  res_num_in_active:                      0
% 3.45/0.99  res_num_of_loops:                       131
% 3.45/0.99  res_forward_subset_subsumed:            24
% 3.45/0.99  res_backward_subset_subsumed:           2
% 3.45/0.99  res_forward_subsumed:                   0
% 3.45/0.99  res_backward_subsumed:                  0
% 3.45/0.99  res_forward_subsumption_resolution:     0
% 3.45/0.99  res_backward_subsumption_resolution:    0
% 3.45/0.99  res_clause_to_clause_subsumption:       2127
% 3.45/0.99  res_orphan_elimination:                 0
% 3.45/0.99  res_tautology_del:                      127
% 3.45/0.99  res_num_eq_res_simplified:              0
% 3.45/0.99  res_num_sel_changes:                    0
% 3.45/0.99  res_moves_from_active_to_pass:          0
% 3.45/0.99  
% 3.45/0.99  ------ Superposition
% 3.45/0.99  
% 3.45/0.99  sup_time_total:                         0.
% 3.45/0.99  sup_time_generating:                    0.
% 3.45/0.99  sup_time_sim_full:                      0.
% 3.45/0.99  sup_time_sim_immed:                     0.
% 3.45/0.99  
% 3.45/0.99  sup_num_of_clauses:                     519
% 3.45/0.99  sup_num_in_active:                      154
% 3.45/0.99  sup_num_in_passive:                     365
% 3.45/0.99  sup_num_of_loops:                       178
% 3.45/0.99  sup_fw_superposition:                   288
% 3.45/0.99  sup_bw_superposition:                   358
% 3.45/0.99  sup_immediate_simplified:               18
% 3.45/0.99  sup_given_eliminated:                   1
% 3.45/0.99  comparisons_done:                       0
% 3.45/0.99  comparisons_avoided:                    0
% 3.45/0.99  
% 3.45/0.99  ------ Simplifications
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  sim_fw_subset_subsumed:                 11
% 3.45/0.99  sim_bw_subset_subsumed:                 11
% 3.45/0.99  sim_fw_subsumed:                        3
% 3.45/0.99  sim_bw_subsumed:                        18
% 3.45/0.99  sim_fw_subsumption_res:                 0
% 3.45/0.99  sim_bw_subsumption_res:                 0
% 3.45/0.99  sim_tautology_del:                      16
% 3.45/0.99  sim_eq_tautology_del:                   0
% 3.45/0.99  sim_eq_res_simp:                        1
% 3.45/0.99  sim_fw_demodulated:                     3
% 3.45/0.99  sim_bw_demodulated:                     4
% 3.45/0.99  sim_light_normalised:                   0
% 3.45/0.99  sim_joinable_taut:                      0
% 3.45/0.99  sim_joinable_simp:                      0
% 3.45/0.99  sim_ac_normalised:                      0
% 3.45/0.99  sim_smt_subsumption:                    0
% 3.45/0.99  
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 11:57:04 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 603 expanded)
%              Number of clauses        :   61 ( 170 expanded)
%              Number of leaves         :   15 ( 144 expanded)
%              Depth                    :   20
%              Number of atoms          :  437 (3831 expanded)
%              Number of equality atoms :  138 ( 302 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
        & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
            & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f34,plain,(
    ! [X4,X2,X3,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X4,X6),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK9,X1)
        & r2_hidden(k4_tarski(X4,sK9),X3)
        & m1_subset_1(sK9,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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

fof(f32,plain,
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
                ( ~ r2_hidden(X5,sK5)
                | ~ r2_hidden(k4_tarski(X4,X5),sK7)
                | ~ m1_subset_1(X5,sK6) )
            | ~ r2_hidden(X4,k8_relset_1(sK4,sK6,sK7,sK5)) )
          & ( ? [X6] :
                ( r2_hidden(X6,sK5)
                & r2_hidden(k4_tarski(X4,X6),sK7)
                & m1_subset_1(X6,sK6) )
            | r2_hidden(X4,k8_relset_1(sK4,sK6,sK7,sK5)) )
          & m1_subset_1(X4,sK4) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
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
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f31,f34,f33,f32])).

fof(f51,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f17])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,
    ( m1_subset_1(sK9,sK6)
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK5)
      | ~ r2_hidden(k4_tarski(sK8,X5),sK7)
      | ~ m1_subset_1(X5,sK6)
      | ~ r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK7)
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f19])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23,f22,f21])).

fof(f42,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f55,plain,
    ( r2_hidden(sK9,sK5)
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_936,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK3(X0,X2,X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_935,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(X0,X2,X1)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_926,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_943,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1978,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK4,sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_943])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_945,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2256,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1978,c_945])).

cnf(c_2801,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(X0,X1,sK7),sK6) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_935,c_2256])).

cnf(c_21,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1100,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1101,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1100])).

cnf(c_4279,plain,
    ( r2_hidden(sK3(X0,X1,sK7),sK6) = iProver_top
    | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2801,c_21,c_1101])).

cnf(c_4280,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(X0,X1,sK7),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_4279])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_942,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4287,plain,
    ( m1_subset_1(sK3(X0,X1,sK7),sK6) = iProver_top
    | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4280,c_942])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK9,sK6)
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_928,plain,
    ( m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,negated_conjecture,
    ( ~ m1_subset_1(X0,sK6)
    | ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(k4_tarski(sK8,X0),sK7)
    | ~ r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_931,plain,
    ( m1_subset_1(X0,sK6) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(sK8,X0),sK7) != iProver_top
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1130,plain,
    ( m1_subset_1(X0,sK6) != iProver_top
    | m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(sK8,X0),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_928,c_931])).

cnf(c_2799,plain,
    ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
    | m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_935,c_1130])).

cnf(c_3233,plain,
    ( r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | m1_subset_1(sK9,sK6) = iProver_top
    | m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2799,c_21,c_1101])).

cnf(c_3234,plain,
    ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
    | m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3233])).

cnf(c_5527,plain,
    ( m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4287,c_3234])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_932,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1962,plain,
    ( k8_relset_1(sK4,sK6,sK7,X0) = k10_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_926,c_932])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(k4_tarski(sK8,sK9),sK7)
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_929,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK7) = iProver_top
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2207,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK7) = iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1962,c_929])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_937,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
    | r2_hidden(X0,k2_relat_1(X3)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_939,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1046,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_937,c_939])).

cnf(c_3281,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(k2_zfmisc_1(sK4,sK6),X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK7) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1978,c_1046])).

cnf(c_3477,plain,
    ( r2_hidden(sK9,X0) != iProver_top
    | r2_hidden(sK8,k10_relat_1(k2_zfmisc_1(sK4,sK6),X0)) = iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2207,c_3281])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK9,sK5)
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_930,plain,
    ( r2_hidden(sK9,sK5) = iProver_top
    | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2208,plain,
    ( r2_hidden(sK9,sK5) = iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1962,c_930])).

cnf(c_3280,plain,
    ( r2_hidden(sK9,X0) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) = iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2207,c_1046])).

cnf(c_3912,plain,
    ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) = iProver_top
    | r2_hidden(sK9,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3280,c_21,c_1101])).

cnf(c_3913,plain,
    ( r2_hidden(sK9,X0) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) = iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3912])).

cnf(c_3923,plain,
    ( r2_hidden(sK9,sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3913])).

cnf(c_3925,plain,
    ( r2_hidden(sK9,sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3923])).

cnf(c_3965,plain,
    ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3477,c_2208,c_3925])).

cnf(c_2210,plain,
    ( m1_subset_1(X0,sK6) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(sK8,X0),sK7) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1962,c_931])).

cnf(c_2796,plain,
    ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
    | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_935,c_2210])).

cnf(c_3255,plain,
    ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2796,c_21,c_1101])).

cnf(c_3256,plain,
    ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
    | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3255])).

cnf(c_5525,plain,
    ( r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4287,c_3256])).

cnf(c_6306,plain,
    ( r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5527,c_2208,c_3925,c_5525])).

cnf(c_6314,plain,
    ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_936,c_6306])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6314,c_3965,c_1101,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:32:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.16/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.01  
% 3.16/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.16/1.01  
% 3.16/1.01  ------  iProver source info
% 3.16/1.01  
% 3.16/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.16/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.16/1.01  git: non_committed_changes: false
% 3.16/1.01  git: last_make_outside_of_git: false
% 3.16/1.01  
% 3.16/1.01  ------ 
% 3.16/1.01  
% 3.16/1.01  ------ Input Options
% 3.16/1.01  
% 3.16/1.01  --out_options                           all
% 3.16/1.01  --tptp_safe_out                         true
% 3.16/1.01  --problem_path                          ""
% 3.16/1.01  --include_path                          ""
% 3.16/1.01  --clausifier                            res/vclausify_rel
% 3.16/1.01  --clausifier_options                    --mode clausify
% 3.16/1.01  --stdin                                 false
% 3.16/1.01  --stats_out                             all
% 3.16/1.01  
% 3.16/1.01  ------ General Options
% 3.16/1.01  
% 3.16/1.01  --fof                                   false
% 3.16/1.01  --time_out_real                         305.
% 3.16/1.01  --time_out_virtual                      -1.
% 3.16/1.01  --symbol_type_check                     false
% 3.16/1.01  --clausify_out                          false
% 3.16/1.01  --sig_cnt_out                           false
% 3.16/1.01  --trig_cnt_out                          false
% 3.16/1.01  --trig_cnt_out_tolerance                1.
% 3.16/1.01  --trig_cnt_out_sk_spl                   false
% 3.16/1.01  --abstr_cl_out                          false
% 3.16/1.01  
% 3.16/1.01  ------ Global Options
% 3.16/1.01  
% 3.16/1.01  --schedule                              default
% 3.16/1.01  --add_important_lit                     false
% 3.16/1.01  --prop_solver_per_cl                    1000
% 3.16/1.01  --min_unsat_core                        false
% 3.16/1.01  --soft_assumptions                      false
% 3.16/1.01  --soft_lemma_size                       3
% 3.16/1.01  --prop_impl_unit_size                   0
% 3.16/1.01  --prop_impl_unit                        []
% 3.16/1.01  --share_sel_clauses                     true
% 3.16/1.01  --reset_solvers                         false
% 3.16/1.01  --bc_imp_inh                            [conj_cone]
% 3.16/1.01  --conj_cone_tolerance                   3.
% 3.16/1.01  --extra_neg_conj                        none
% 3.16/1.01  --large_theory_mode                     true
% 3.16/1.01  --prolific_symb_bound                   200
% 3.16/1.01  --lt_threshold                          2000
% 3.16/1.01  --clause_weak_htbl                      true
% 3.16/1.01  --gc_record_bc_elim                     false
% 3.16/1.01  
% 3.16/1.01  ------ Preprocessing Options
% 3.16/1.01  
% 3.16/1.01  --preprocessing_flag                    true
% 3.16/1.01  --time_out_prep_mult                    0.1
% 3.16/1.01  --splitting_mode                        input
% 3.16/1.01  --splitting_grd                         true
% 3.16/1.01  --splitting_cvd                         false
% 3.16/1.01  --splitting_cvd_svl                     false
% 3.16/1.01  --splitting_nvd                         32
% 3.16/1.01  --sub_typing                            true
% 3.16/1.01  --prep_gs_sim                           true
% 3.16/1.01  --prep_unflatten                        true
% 3.16/1.01  --prep_res_sim                          true
% 3.16/1.01  --prep_upred                            true
% 3.16/1.01  --prep_sem_filter                       exhaustive
% 3.16/1.01  --prep_sem_filter_out                   false
% 3.16/1.01  --pred_elim                             true
% 3.16/1.01  --res_sim_input                         true
% 3.16/1.01  --eq_ax_congr_red                       true
% 3.16/1.01  --pure_diseq_elim                       true
% 3.16/1.01  --brand_transform                       false
% 3.16/1.01  --non_eq_to_eq                          false
% 3.16/1.01  --prep_def_merge                        true
% 3.16/1.01  --prep_def_merge_prop_impl              false
% 3.16/1.01  --prep_def_merge_mbd                    true
% 3.16/1.01  --prep_def_merge_tr_red                 false
% 3.16/1.01  --prep_def_merge_tr_cl                  false
% 3.16/1.01  --smt_preprocessing                     true
% 3.16/1.01  --smt_ac_axioms                         fast
% 3.16/1.01  --preprocessed_out                      false
% 3.16/1.01  --preprocessed_stats                    false
% 3.16/1.01  
% 3.16/1.01  ------ Abstraction refinement Options
% 3.16/1.01  
% 3.16/1.01  --abstr_ref                             []
% 3.16/1.01  --abstr_ref_prep                        false
% 3.16/1.01  --abstr_ref_until_sat                   false
% 3.16/1.01  --abstr_ref_sig_restrict                funpre
% 3.16/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/1.01  --abstr_ref_under                       []
% 3.16/1.01  
% 3.16/1.01  ------ SAT Options
% 3.16/1.01  
% 3.16/1.01  --sat_mode                              false
% 3.16/1.01  --sat_fm_restart_options                ""
% 3.16/1.01  --sat_gr_def                            false
% 3.16/1.01  --sat_epr_types                         true
% 3.16/1.01  --sat_non_cyclic_types                  false
% 3.16/1.01  --sat_finite_models                     false
% 3.16/1.01  --sat_fm_lemmas                         false
% 3.16/1.01  --sat_fm_prep                           false
% 3.16/1.01  --sat_fm_uc_incr                        true
% 3.16/1.01  --sat_out_model                         small
% 3.16/1.01  --sat_out_clauses                       false
% 3.16/1.01  
% 3.16/1.01  ------ QBF Options
% 3.16/1.01  
% 3.16/1.01  --qbf_mode                              false
% 3.16/1.01  --qbf_elim_univ                         false
% 3.16/1.01  --qbf_dom_inst                          none
% 3.16/1.01  --qbf_dom_pre_inst                      false
% 3.16/1.01  --qbf_sk_in                             false
% 3.16/1.01  --qbf_pred_elim                         true
% 3.16/1.01  --qbf_split                             512
% 3.16/1.01  
% 3.16/1.01  ------ BMC1 Options
% 3.16/1.01  
% 3.16/1.01  --bmc1_incremental                      false
% 3.16/1.01  --bmc1_axioms                           reachable_all
% 3.16/1.01  --bmc1_min_bound                        0
% 3.16/1.01  --bmc1_max_bound                        -1
% 3.16/1.01  --bmc1_max_bound_default                -1
% 3.16/1.01  --bmc1_symbol_reachability              true
% 3.16/1.01  --bmc1_property_lemmas                  false
% 3.16/1.01  --bmc1_k_induction                      false
% 3.16/1.01  --bmc1_non_equiv_states                 false
% 3.16/1.01  --bmc1_deadlock                         false
% 3.16/1.01  --bmc1_ucm                              false
% 3.16/1.01  --bmc1_add_unsat_core                   none
% 3.16/1.01  --bmc1_unsat_core_children              false
% 3.16/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/1.01  --bmc1_out_stat                         full
% 3.16/1.01  --bmc1_ground_init                      false
% 3.16/1.01  --bmc1_pre_inst_next_state              false
% 3.16/1.01  --bmc1_pre_inst_state                   false
% 3.16/1.01  --bmc1_pre_inst_reach_state             false
% 3.16/1.01  --bmc1_out_unsat_core                   false
% 3.16/1.01  --bmc1_aig_witness_out                  false
% 3.16/1.01  --bmc1_verbose                          false
% 3.16/1.01  --bmc1_dump_clauses_tptp                false
% 3.16/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.16/1.01  --bmc1_dump_file                        -
% 3.16/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.16/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.16/1.01  --bmc1_ucm_extend_mode                  1
% 3.16/1.01  --bmc1_ucm_init_mode                    2
% 3.16/1.01  --bmc1_ucm_cone_mode                    none
% 3.16/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.16/1.01  --bmc1_ucm_relax_model                  4
% 3.16/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.16/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/1.01  --bmc1_ucm_layered_model                none
% 3.16/1.01  --bmc1_ucm_max_lemma_size               10
% 3.16/1.01  
% 3.16/1.01  ------ AIG Options
% 3.16/1.01  
% 3.16/1.01  --aig_mode                              false
% 3.16/1.01  
% 3.16/1.01  ------ Instantiation Options
% 3.16/1.01  
% 3.16/1.01  --instantiation_flag                    true
% 3.16/1.01  --inst_sos_flag                         false
% 3.16/1.01  --inst_sos_phase                        true
% 3.16/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/1.01  --inst_lit_sel_side                     num_symb
% 3.16/1.01  --inst_solver_per_active                1400
% 3.16/1.01  --inst_solver_calls_frac                1.
% 3.16/1.01  --inst_passive_queue_type               priority_queues
% 3.16/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/1.01  --inst_passive_queues_freq              [25;2]
% 3.16/1.01  --inst_dismatching                      true
% 3.16/1.01  --inst_eager_unprocessed_to_passive     true
% 3.16/1.01  --inst_prop_sim_given                   true
% 3.16/1.01  --inst_prop_sim_new                     false
% 3.16/1.01  --inst_subs_new                         false
% 3.16/1.01  --inst_eq_res_simp                      false
% 3.16/1.01  --inst_subs_given                       false
% 3.16/1.01  --inst_orphan_elimination               true
% 3.16/1.01  --inst_learning_loop_flag               true
% 3.16/1.01  --inst_learning_start                   3000
% 3.16/1.01  --inst_learning_factor                  2
% 3.16/1.01  --inst_start_prop_sim_after_learn       3
% 3.16/1.01  --inst_sel_renew                        solver
% 3.16/1.01  --inst_lit_activity_flag                true
% 3.16/1.01  --inst_restr_to_given                   false
% 3.16/1.01  --inst_activity_threshold               500
% 3.16/1.01  --inst_out_proof                        true
% 3.16/1.01  
% 3.16/1.01  ------ Resolution Options
% 3.16/1.01  
% 3.16/1.01  --resolution_flag                       true
% 3.16/1.01  --res_lit_sel                           adaptive
% 3.16/1.01  --res_lit_sel_side                      none
% 3.16/1.01  --res_ordering                          kbo
% 3.16/1.01  --res_to_prop_solver                    active
% 3.16/1.01  --res_prop_simpl_new                    false
% 3.16/1.01  --res_prop_simpl_given                  true
% 3.16/1.01  --res_passive_queue_type                priority_queues
% 3.16/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/1.01  --res_passive_queues_freq               [15;5]
% 3.16/1.01  --res_forward_subs                      full
% 3.16/1.01  --res_backward_subs                     full
% 3.16/1.01  --res_forward_subs_resolution           true
% 3.16/1.01  --res_backward_subs_resolution          true
% 3.16/1.01  --res_orphan_elimination                true
% 3.16/1.01  --res_time_limit                        2.
% 3.16/1.01  --res_out_proof                         true
% 3.16/1.01  
% 3.16/1.01  ------ Superposition Options
% 3.16/1.01  
% 3.16/1.01  --superposition_flag                    true
% 3.16/1.01  --sup_passive_queue_type                priority_queues
% 3.16/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.16/1.01  --demod_completeness_check              fast
% 3.16/1.01  --demod_use_ground                      true
% 3.16/1.01  --sup_to_prop_solver                    passive
% 3.16/1.01  --sup_prop_simpl_new                    true
% 3.16/1.01  --sup_prop_simpl_given                  true
% 3.16/1.01  --sup_fun_splitting                     false
% 3.16/1.01  --sup_smt_interval                      50000
% 3.16/1.01  
% 3.16/1.01  ------ Superposition Simplification Setup
% 3.16/1.01  
% 3.16/1.01  --sup_indices_passive                   []
% 3.16/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.01  --sup_full_bw                           [BwDemod]
% 3.16/1.01  --sup_immed_triv                        [TrivRules]
% 3.16/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.01  --sup_immed_bw_main                     []
% 3.16/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.01  
% 3.16/1.01  ------ Combination Options
% 3.16/1.01  
% 3.16/1.01  --comb_res_mult                         3
% 3.16/1.01  --comb_sup_mult                         2
% 3.16/1.01  --comb_inst_mult                        10
% 3.16/1.01  
% 3.16/1.01  ------ Debug Options
% 3.16/1.01  
% 3.16/1.01  --dbg_backtrace                         false
% 3.16/1.01  --dbg_dump_prop_clauses                 false
% 3.16/1.01  --dbg_dump_prop_clauses_file            -
% 3.16/1.01  --dbg_out_stat                          false
% 3.16/1.01  ------ Parsing...
% 3.16/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.16/1.01  
% 3.16/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.16/1.01  
% 3.16/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.16/1.01  
% 3.16/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.16/1.01  ------ Proving...
% 3.16/1.01  ------ Problem Properties 
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  clauses                                 21
% 3.16/1.01  conjectures                             6
% 3.16/1.01  EPR                                     2
% 3.16/1.01  Horn                                    17
% 3.16/1.01  unary                                   2
% 3.16/1.01  binary                                  10
% 3.16/1.01  lits                                    52
% 3.16/1.01  lits eq                                 3
% 3.16/1.01  fd_pure                                 0
% 3.16/1.01  fd_pseudo                               0
% 3.16/1.01  fd_cond                                 0
% 3.16/1.01  fd_pseudo_cond                          2
% 3.16/1.01  AC symbols                              0
% 3.16/1.01  
% 3.16/1.01  ------ Schedule dynamic 5 is on 
% 3.16/1.01  
% 3.16/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  ------ 
% 3.16/1.01  Current options:
% 3.16/1.01  ------ 
% 3.16/1.01  
% 3.16/1.01  ------ Input Options
% 3.16/1.01  
% 3.16/1.01  --out_options                           all
% 3.16/1.01  --tptp_safe_out                         true
% 3.16/1.01  --problem_path                          ""
% 3.16/1.01  --include_path                          ""
% 3.16/1.01  --clausifier                            res/vclausify_rel
% 3.16/1.01  --clausifier_options                    --mode clausify
% 3.16/1.01  --stdin                                 false
% 3.16/1.01  --stats_out                             all
% 3.16/1.01  
% 3.16/1.01  ------ General Options
% 3.16/1.01  
% 3.16/1.01  --fof                                   false
% 3.16/1.01  --time_out_real                         305.
% 3.16/1.01  --time_out_virtual                      -1.
% 3.16/1.01  --symbol_type_check                     false
% 3.16/1.01  --clausify_out                          false
% 3.16/1.01  --sig_cnt_out                           false
% 3.16/1.01  --trig_cnt_out                          false
% 3.16/1.01  --trig_cnt_out_tolerance                1.
% 3.16/1.01  --trig_cnt_out_sk_spl                   false
% 3.16/1.01  --abstr_cl_out                          false
% 3.16/1.01  
% 3.16/1.01  ------ Global Options
% 3.16/1.01  
% 3.16/1.01  --schedule                              default
% 3.16/1.01  --add_important_lit                     false
% 3.16/1.01  --prop_solver_per_cl                    1000
% 3.16/1.01  --min_unsat_core                        false
% 3.16/1.01  --soft_assumptions                      false
% 3.16/1.01  --soft_lemma_size                       3
% 3.16/1.01  --prop_impl_unit_size                   0
% 3.16/1.01  --prop_impl_unit                        []
% 3.16/1.01  --share_sel_clauses                     true
% 3.16/1.01  --reset_solvers                         false
% 3.16/1.01  --bc_imp_inh                            [conj_cone]
% 3.16/1.01  --conj_cone_tolerance                   3.
% 3.16/1.01  --extra_neg_conj                        none
% 3.16/1.01  --large_theory_mode                     true
% 3.16/1.01  --prolific_symb_bound                   200
% 3.16/1.01  --lt_threshold                          2000
% 3.16/1.01  --clause_weak_htbl                      true
% 3.16/1.01  --gc_record_bc_elim                     false
% 3.16/1.01  
% 3.16/1.01  ------ Preprocessing Options
% 3.16/1.01  
% 3.16/1.01  --preprocessing_flag                    true
% 3.16/1.01  --time_out_prep_mult                    0.1
% 3.16/1.01  --splitting_mode                        input
% 3.16/1.01  --splitting_grd                         true
% 3.16/1.01  --splitting_cvd                         false
% 3.16/1.01  --splitting_cvd_svl                     false
% 3.16/1.01  --splitting_nvd                         32
% 3.16/1.01  --sub_typing                            true
% 3.16/1.01  --prep_gs_sim                           true
% 3.16/1.01  --prep_unflatten                        true
% 3.16/1.01  --prep_res_sim                          true
% 3.16/1.01  --prep_upred                            true
% 3.16/1.01  --prep_sem_filter                       exhaustive
% 3.16/1.01  --prep_sem_filter_out                   false
% 3.16/1.01  --pred_elim                             true
% 3.16/1.01  --res_sim_input                         true
% 3.16/1.01  --eq_ax_congr_red                       true
% 3.16/1.01  --pure_diseq_elim                       true
% 3.16/1.01  --brand_transform                       false
% 3.16/1.01  --non_eq_to_eq                          false
% 3.16/1.01  --prep_def_merge                        true
% 3.16/1.01  --prep_def_merge_prop_impl              false
% 3.16/1.01  --prep_def_merge_mbd                    true
% 3.16/1.01  --prep_def_merge_tr_red                 false
% 3.16/1.01  --prep_def_merge_tr_cl                  false
% 3.16/1.01  --smt_preprocessing                     true
% 3.16/1.01  --smt_ac_axioms                         fast
% 3.16/1.01  --preprocessed_out                      false
% 3.16/1.01  --preprocessed_stats                    false
% 3.16/1.01  
% 3.16/1.01  ------ Abstraction refinement Options
% 3.16/1.01  
% 3.16/1.01  --abstr_ref                             []
% 3.16/1.01  --abstr_ref_prep                        false
% 3.16/1.01  --abstr_ref_until_sat                   false
% 3.16/1.01  --abstr_ref_sig_restrict                funpre
% 3.16/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/1.01  --abstr_ref_under                       []
% 3.16/1.01  
% 3.16/1.01  ------ SAT Options
% 3.16/1.01  
% 3.16/1.01  --sat_mode                              false
% 3.16/1.01  --sat_fm_restart_options                ""
% 3.16/1.01  --sat_gr_def                            false
% 3.16/1.01  --sat_epr_types                         true
% 3.16/1.01  --sat_non_cyclic_types                  false
% 3.16/1.01  --sat_finite_models                     false
% 3.16/1.01  --sat_fm_lemmas                         false
% 3.16/1.01  --sat_fm_prep                           false
% 3.16/1.01  --sat_fm_uc_incr                        true
% 3.16/1.01  --sat_out_model                         small
% 3.16/1.01  --sat_out_clauses                       false
% 3.16/1.01  
% 3.16/1.01  ------ QBF Options
% 3.16/1.01  
% 3.16/1.01  --qbf_mode                              false
% 3.16/1.01  --qbf_elim_univ                         false
% 3.16/1.01  --qbf_dom_inst                          none
% 3.16/1.01  --qbf_dom_pre_inst                      false
% 3.16/1.01  --qbf_sk_in                             false
% 3.16/1.01  --qbf_pred_elim                         true
% 3.16/1.01  --qbf_split                             512
% 3.16/1.01  
% 3.16/1.01  ------ BMC1 Options
% 3.16/1.01  
% 3.16/1.01  --bmc1_incremental                      false
% 3.16/1.01  --bmc1_axioms                           reachable_all
% 3.16/1.01  --bmc1_min_bound                        0
% 3.16/1.01  --bmc1_max_bound                        -1
% 3.16/1.01  --bmc1_max_bound_default                -1
% 3.16/1.01  --bmc1_symbol_reachability              true
% 3.16/1.01  --bmc1_property_lemmas                  false
% 3.16/1.01  --bmc1_k_induction                      false
% 3.16/1.01  --bmc1_non_equiv_states                 false
% 3.16/1.01  --bmc1_deadlock                         false
% 3.16/1.01  --bmc1_ucm                              false
% 3.16/1.01  --bmc1_add_unsat_core                   none
% 3.16/1.01  --bmc1_unsat_core_children              false
% 3.16/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/1.01  --bmc1_out_stat                         full
% 3.16/1.01  --bmc1_ground_init                      false
% 3.16/1.01  --bmc1_pre_inst_next_state              false
% 3.16/1.01  --bmc1_pre_inst_state                   false
% 3.16/1.01  --bmc1_pre_inst_reach_state             false
% 3.16/1.01  --bmc1_out_unsat_core                   false
% 3.16/1.01  --bmc1_aig_witness_out                  false
% 3.16/1.01  --bmc1_verbose                          false
% 3.16/1.01  --bmc1_dump_clauses_tptp                false
% 3.16/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.16/1.01  --bmc1_dump_file                        -
% 3.16/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.16/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.16/1.01  --bmc1_ucm_extend_mode                  1
% 3.16/1.01  --bmc1_ucm_init_mode                    2
% 3.16/1.01  --bmc1_ucm_cone_mode                    none
% 3.16/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.16/1.01  --bmc1_ucm_relax_model                  4
% 3.16/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.16/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/1.01  --bmc1_ucm_layered_model                none
% 3.16/1.01  --bmc1_ucm_max_lemma_size               10
% 3.16/1.01  
% 3.16/1.01  ------ AIG Options
% 3.16/1.01  
% 3.16/1.01  --aig_mode                              false
% 3.16/1.01  
% 3.16/1.01  ------ Instantiation Options
% 3.16/1.01  
% 3.16/1.01  --instantiation_flag                    true
% 3.16/1.01  --inst_sos_flag                         false
% 3.16/1.01  --inst_sos_phase                        true
% 3.16/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/1.01  --inst_lit_sel_side                     none
% 3.16/1.01  --inst_solver_per_active                1400
% 3.16/1.01  --inst_solver_calls_frac                1.
% 3.16/1.01  --inst_passive_queue_type               priority_queues
% 3.16/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/1.01  --inst_passive_queues_freq              [25;2]
% 3.16/1.01  --inst_dismatching                      true
% 3.16/1.01  --inst_eager_unprocessed_to_passive     true
% 3.16/1.01  --inst_prop_sim_given                   true
% 3.16/1.01  --inst_prop_sim_new                     false
% 3.16/1.01  --inst_subs_new                         false
% 3.16/1.01  --inst_eq_res_simp                      false
% 3.16/1.01  --inst_subs_given                       false
% 3.16/1.01  --inst_orphan_elimination               true
% 3.16/1.01  --inst_learning_loop_flag               true
% 3.16/1.01  --inst_learning_start                   3000
% 3.16/1.01  --inst_learning_factor                  2
% 3.16/1.01  --inst_start_prop_sim_after_learn       3
% 3.16/1.01  --inst_sel_renew                        solver
% 3.16/1.01  --inst_lit_activity_flag                true
% 3.16/1.01  --inst_restr_to_given                   false
% 3.16/1.01  --inst_activity_threshold               500
% 3.16/1.01  --inst_out_proof                        true
% 3.16/1.01  
% 3.16/1.01  ------ Resolution Options
% 3.16/1.01  
% 3.16/1.01  --resolution_flag                       false
% 3.16/1.01  --res_lit_sel                           adaptive
% 3.16/1.01  --res_lit_sel_side                      none
% 3.16/1.01  --res_ordering                          kbo
% 3.16/1.01  --res_to_prop_solver                    active
% 3.16/1.01  --res_prop_simpl_new                    false
% 3.16/1.01  --res_prop_simpl_given                  true
% 3.16/1.01  --res_passive_queue_type                priority_queues
% 3.16/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/1.01  --res_passive_queues_freq               [15;5]
% 3.16/1.01  --res_forward_subs                      full
% 3.16/1.01  --res_backward_subs                     full
% 3.16/1.01  --res_forward_subs_resolution           true
% 3.16/1.01  --res_backward_subs_resolution          true
% 3.16/1.01  --res_orphan_elimination                true
% 3.16/1.01  --res_time_limit                        2.
% 3.16/1.01  --res_out_proof                         true
% 3.16/1.01  
% 3.16/1.01  ------ Superposition Options
% 3.16/1.01  
% 3.16/1.01  --superposition_flag                    true
% 3.16/1.01  --sup_passive_queue_type                priority_queues
% 3.16/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.16/1.01  --demod_completeness_check              fast
% 3.16/1.01  --demod_use_ground                      true
% 3.16/1.01  --sup_to_prop_solver                    passive
% 3.16/1.01  --sup_prop_simpl_new                    true
% 3.16/1.01  --sup_prop_simpl_given                  true
% 3.16/1.01  --sup_fun_splitting                     false
% 3.16/1.01  --sup_smt_interval                      50000
% 3.16/1.01  
% 3.16/1.01  ------ Superposition Simplification Setup
% 3.16/1.01  
% 3.16/1.01  --sup_indices_passive                   []
% 3.16/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.01  --sup_full_bw                           [BwDemod]
% 3.16/1.01  --sup_immed_triv                        [TrivRules]
% 3.16/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.01  --sup_immed_bw_main                     []
% 3.16/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.01  
% 3.16/1.01  ------ Combination Options
% 3.16/1.01  
% 3.16/1.01  --comb_res_mult                         3
% 3.16/1.01  --comb_sup_mult                         2
% 3.16/1.01  --comb_inst_mult                        10
% 3.16/1.01  
% 3.16/1.01  ------ Debug Options
% 3.16/1.01  
% 3.16/1.01  --dbg_backtrace                         false
% 3.16/1.01  --dbg_dump_prop_clauses                 false
% 3.16/1.01  --dbg_dump_prop_clauses_file            -
% 3.16/1.01  --dbg_out_stat                          false
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  ------ Proving...
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  % SZS status Theorem for theBenchmark.p
% 3.16/1.01  
% 3.16/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.16/1.01  
% 3.16/1.01  fof(f5,axiom,(
% 3.16/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f13,plain,(
% 3.16/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.16/1.01    inference(ennf_transformation,[],[f5])).
% 3.16/1.01  
% 3.16/1.01  fof(f25,plain,(
% 3.16/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.16/1.01    inference(nnf_transformation,[],[f13])).
% 3.16/1.01  
% 3.16/1.01  fof(f26,plain,(
% 3.16/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.16/1.01    inference(rectify,[],[f25])).
% 3.16/1.01  
% 3.16/1.01  fof(f27,plain,(
% 3.16/1.01    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))))),
% 3.16/1.01    introduced(choice_axiom,[])).
% 3.16/1.01  
% 3.16/1.01  fof(f28,plain,(
% 3.16/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.16/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 3.16/1.01  
% 3.16/1.01  fof(f47,plain,(
% 3.16/1.01    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f28])).
% 3.16/1.01  
% 3.16/1.01  fof(f46,plain,(
% 3.16/1.01    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f28])).
% 3.16/1.01  
% 3.16/1.01  fof(f8,conjecture,(
% 3.16/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f9,negated_conjecture,(
% 3.16/1.01    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 3.16/1.01    inference(negated_conjecture,[],[f8])).
% 3.16/1.01  
% 3.16/1.01  fof(f10,plain,(
% 3.16/1.01    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)))))),
% 3.16/1.01    inference(pure_predicate_removal,[],[f9])).
% 3.16/1.01  
% 3.16/1.01  fof(f16,plain,(
% 3.16/1.01    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.16/1.01    inference(ennf_transformation,[],[f10])).
% 3.16/1.01  
% 3.16/1.01  fof(f29,plain,(
% 3.16/1.01    ? [X0,X1,X2,X3] : (? [X4] : (((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.16/1.01    inference(nnf_transformation,[],[f16])).
% 3.16/1.01  
% 3.16/1.01  fof(f30,plain,(
% 3.16/1.01    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.16/1.01    inference(flattening,[],[f29])).
% 3.16/1.01  
% 3.16/1.01  fof(f31,plain,(
% 3.16/1.01    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.16/1.01    inference(rectify,[],[f30])).
% 3.16/1.01  
% 3.16/1.01  fof(f34,plain,(
% 3.16/1.01    ( ! [X4,X2,X3,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK9,X1) & r2_hidden(k4_tarski(X4,sK9),X3) & m1_subset_1(sK9,X2))) )),
% 3.16/1.01    introduced(choice_axiom,[])).
% 3.16/1.01  
% 3.16/1.01  fof(f33,plain,(
% 3.16/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) => ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(sK8,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(sK8,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(sK8,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(sK8,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(sK8,X0))) )),
% 3.16/1.01    introduced(choice_axiom,[])).
% 3.16/1.01  
% 3.16/1.01  fof(f32,plain,(
% 3.16/1.01    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (? [X4] : ((! [X5] : (~r2_hidden(X5,sK5) | ~r2_hidden(k4_tarski(X4,X5),sK7) | ~m1_subset_1(X5,sK6)) | ~r2_hidden(X4,k8_relset_1(sK4,sK6,sK7,sK5))) & (? [X6] : (r2_hidden(X6,sK5) & r2_hidden(k4_tarski(X4,X6),sK7) & m1_subset_1(X6,sK6)) | r2_hidden(X4,k8_relset_1(sK4,sK6,sK7,sK5))) & m1_subset_1(X4,sK4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))))),
% 3.16/1.01    introduced(choice_axiom,[])).
% 3.16/1.01  
% 3.16/1.01  fof(f35,plain,(
% 3.16/1.01    ((! [X5] : (~r2_hidden(X5,sK5) | ~r2_hidden(k4_tarski(sK8,X5),sK7) | ~m1_subset_1(X5,sK6)) | ~r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5))) & ((r2_hidden(sK9,sK5) & r2_hidden(k4_tarski(sK8,sK9),sK7) & m1_subset_1(sK9,sK6)) | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5))) & m1_subset_1(sK8,sK4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))),
% 3.16/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f31,f34,f33,f32])).
% 3.16/1.01  
% 3.16/1.01  fof(f51,plain,(
% 3.16/1.01    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))),
% 3.16/1.01    inference(cnf_transformation,[],[f35])).
% 3.16/1.01  
% 3.16/1.01  fof(f2,axiom,(
% 3.16/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f11,plain,(
% 3.16/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.16/1.01    inference(ennf_transformation,[],[f2])).
% 3.16/1.01  
% 3.16/1.01  fof(f39,plain,(
% 3.16/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.16/1.01    inference(cnf_transformation,[],[f11])).
% 3.16/1.01  
% 3.16/1.01  fof(f1,axiom,(
% 3.16/1.01    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f17,plain,(
% 3.16/1.01    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.16/1.01    inference(nnf_transformation,[],[f1])).
% 3.16/1.01  
% 3.16/1.01  fof(f18,plain,(
% 3.16/1.01    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.16/1.01    inference(flattening,[],[f17])).
% 3.16/1.01  
% 3.16/1.01  fof(f37,plain,(
% 3.16/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.16/1.01    inference(cnf_transformation,[],[f18])).
% 3.16/1.01  
% 3.16/1.01  fof(f6,axiom,(
% 3.16/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f14,plain,(
% 3.16/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.01    inference(ennf_transformation,[],[f6])).
% 3.16/1.01  
% 3.16/1.01  fof(f49,plain,(
% 3.16/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.01    inference(cnf_transformation,[],[f14])).
% 3.16/1.01  
% 3.16/1.01  fof(f3,axiom,(
% 3.16/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f12,plain,(
% 3.16/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.16/1.01    inference(ennf_transformation,[],[f3])).
% 3.16/1.01  
% 3.16/1.01  fof(f40,plain,(
% 3.16/1.01    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f12])).
% 3.16/1.01  
% 3.16/1.01  fof(f53,plain,(
% 3.16/1.01    m1_subset_1(sK9,sK6) | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5))),
% 3.16/1.01    inference(cnf_transformation,[],[f35])).
% 3.16/1.01  
% 3.16/1.01  fof(f56,plain,(
% 3.16/1.01    ( ! [X5] : (~r2_hidden(X5,sK5) | ~r2_hidden(k4_tarski(sK8,X5),sK7) | ~m1_subset_1(X5,sK6) | ~r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5))) )),
% 3.16/1.01    inference(cnf_transformation,[],[f35])).
% 3.16/1.01  
% 3.16/1.01  fof(f7,axiom,(
% 3.16/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f15,plain,(
% 3.16/1.01    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.01    inference(ennf_transformation,[],[f7])).
% 3.16/1.01  
% 3.16/1.01  fof(f50,plain,(
% 3.16/1.01    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.01    inference(cnf_transformation,[],[f15])).
% 3.16/1.01  
% 3.16/1.01  fof(f54,plain,(
% 3.16/1.01    r2_hidden(k4_tarski(sK8,sK9),sK7) | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5))),
% 3.16/1.01    inference(cnf_transformation,[],[f35])).
% 3.16/1.01  
% 3.16/1.01  fof(f48,plain,(
% 3.16/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f28])).
% 3.16/1.01  
% 3.16/1.01  fof(f4,axiom,(
% 3.16/1.01    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f19,plain,(
% 3.16/1.01    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.16/1.01    inference(nnf_transformation,[],[f4])).
% 3.16/1.01  
% 3.16/1.01  fof(f20,plain,(
% 3.16/1.01    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.16/1.01    inference(rectify,[],[f19])).
% 3.16/1.01  
% 3.16/1.01  fof(f23,plain,(
% 3.16/1.01    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0))),
% 3.16/1.01    introduced(choice_axiom,[])).
% 3.16/1.01  
% 3.16/1.01  fof(f22,plain,(
% 3.16/1.01    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0))) )),
% 3.16/1.01    introduced(choice_axiom,[])).
% 3.16/1.01  
% 3.16/1.01  fof(f21,plain,(
% 3.16/1.01    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.16/1.01    introduced(choice_axiom,[])).
% 3.16/1.01  
% 3.16/1.01  fof(f24,plain,(
% 3.16/1.01    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.16/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23,f22,f21])).
% 3.16/1.01  
% 3.16/1.01  fof(f42,plain,(
% 3.16/1.01    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 3.16/1.01    inference(cnf_transformation,[],[f24])).
% 3.16/1.01  
% 3.16/1.01  fof(f57,plain,(
% 3.16/1.01    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 3.16/1.01    inference(equality_resolution,[],[f42])).
% 3.16/1.01  
% 3.16/1.01  fof(f55,plain,(
% 3.16/1.01    r2_hidden(sK9,sK5) | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5))),
% 3.16/1.01    inference(cnf_transformation,[],[f35])).
% 3.16/1.01  
% 3.16/1.01  cnf(c_10,plain,
% 3.16/1.01      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.16/1.01      | r2_hidden(sK3(X0,X2,X1),X2)
% 3.16/1.01      | ~ v1_relat_1(X1) ),
% 3.16/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_936,plain,
% 3.16/1.01      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 3.16/1.01      | r2_hidden(sK3(X0,X2,X1),X2) = iProver_top
% 3.16/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_11,plain,
% 3.16/1.01      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.16/1.01      | r2_hidden(k4_tarski(X0,sK3(X0,X2,X1)),X1)
% 3.16/1.01      | ~ v1_relat_1(X1) ),
% 3.16/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_935,plain,
% 3.16/1.01      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 3.16/1.01      | r2_hidden(k4_tarski(X0,sK3(X0,X2,X1)),X1) = iProver_top
% 3.16/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_20,negated_conjecture,
% 3.16/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
% 3.16/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_926,plain,
% 3.16/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3,plain,
% 3.16/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.16/1.01      | ~ r2_hidden(X2,X0)
% 3.16/1.01      | r2_hidden(X2,X1) ),
% 3.16/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_943,plain,
% 3.16/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.16/1.01      | r2_hidden(X2,X0) != iProver_top
% 3.16/1.01      | r2_hidden(X2,X1) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1978,plain,
% 3.16/1.01      ( r2_hidden(X0,k2_zfmisc_1(sK4,sK6)) = iProver_top
% 3.16/1.01      | r2_hidden(X0,sK7) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_926,c_943]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1,plain,
% 3.16/1.01      ( r2_hidden(X0,X1)
% 3.16/1.01      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.16/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_945,plain,
% 3.16/1.01      ( r2_hidden(X0,X1) = iProver_top
% 3.16/1.01      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2256,plain,
% 3.16/1.01      ( r2_hidden(X0,sK6) = iProver_top
% 3.16/1.01      | r2_hidden(k4_tarski(X1,X0),sK7) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_1978,c_945]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2801,plain,
% 3.16/1.01      ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 3.16/1.01      | r2_hidden(sK3(X0,X1,sK7),sK6) = iProver_top
% 3.16/1.01      | v1_relat_1(sK7) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_935,c_2256]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_21,plain,
% 3.16/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_13,plain,
% 3.16/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.01      | v1_relat_1(X0) ),
% 3.16/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1100,plain,
% 3.16/1.01      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
% 3.16/1.01      | v1_relat_1(sK7) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1101,plain,
% 3.16/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) != iProver_top
% 3.16/1.01      | v1_relat_1(sK7) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_1100]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_4279,plain,
% 3.16/1.01      ( r2_hidden(sK3(X0,X1,sK7),sK6) = iProver_top
% 3.16/1.01      | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_2801,c_21,c_1101]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_4280,plain,
% 3.16/1.01      ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 3.16/1.01      | r2_hidden(sK3(X0,X1,sK7),sK6) = iProver_top ),
% 3.16/1.01      inference(renaming,[status(thm)],[c_4279]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_4,plain,
% 3.16/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.16/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_942,plain,
% 3.16/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 3.16/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_4287,plain,
% 3.16/1.01      ( m1_subset_1(sK3(X0,X1,sK7),sK6) = iProver_top
% 3.16/1.01      | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_4280,c_942]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_18,negated_conjecture,
% 3.16/1.01      ( m1_subset_1(sK9,sK6)
% 3.16/1.01      | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
% 3.16/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_928,plain,
% 3.16/1.01      ( m1_subset_1(sK9,sK6) = iProver_top
% 3.16/1.01      | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_15,negated_conjecture,
% 3.16/1.01      ( ~ m1_subset_1(X0,sK6)
% 3.16/1.01      | ~ r2_hidden(X0,sK5)
% 3.16/1.01      | ~ r2_hidden(k4_tarski(sK8,X0),sK7)
% 3.16/1.01      | ~ r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
% 3.16/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_931,plain,
% 3.16/1.01      ( m1_subset_1(X0,sK6) != iProver_top
% 3.16/1.01      | r2_hidden(X0,sK5) != iProver_top
% 3.16/1.01      | r2_hidden(k4_tarski(sK8,X0),sK7) != iProver_top
% 3.16/1.01      | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1130,plain,
% 3.16/1.01      ( m1_subset_1(X0,sK6) != iProver_top
% 3.16/1.01      | m1_subset_1(sK9,sK6) = iProver_top
% 3.16/1.01      | r2_hidden(X0,sK5) != iProver_top
% 3.16/1.01      | r2_hidden(k4_tarski(sK8,X0),sK7) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_928,c_931]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2799,plain,
% 3.16/1.01      ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
% 3.16/1.01      | m1_subset_1(sK9,sK6) = iProver_top
% 3.16/1.01      | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
% 3.16/1.01      | v1_relat_1(sK7) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_935,c_1130]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3233,plain,
% 3.16/1.01      ( r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
% 3.16/1.01      | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 3.16/1.01      | m1_subset_1(sK9,sK6) = iProver_top
% 3.16/1.01      | m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_2799,c_21,c_1101]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3234,plain,
% 3.16/1.01      ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
% 3.16/1.01      | m1_subset_1(sK9,sK6) = iProver_top
% 3.16/1.01      | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top ),
% 3.16/1.01      inference(renaming,[status(thm)],[c_3233]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_5527,plain,
% 3.16/1.01      ( m1_subset_1(sK9,sK6) = iProver_top
% 3.16/1.01      | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_4287,c_3234]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_14,plain,
% 3.16/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.01      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.16/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_932,plain,
% 3.16/1.01      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.16/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1962,plain,
% 3.16/1.01      ( k8_relset_1(sK4,sK6,sK7,X0) = k10_relat_1(sK7,X0) ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_926,c_932]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_17,negated_conjecture,
% 3.16/1.01      ( r2_hidden(k4_tarski(sK8,sK9),sK7)
% 3.16/1.01      | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
% 3.16/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_929,plain,
% 3.16/1.01      ( r2_hidden(k4_tarski(sK8,sK9),sK7) = iProver_top
% 3.16/1.01      | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2207,plain,
% 3.16/1.01      ( r2_hidden(k4_tarski(sK8,sK9),sK7) = iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
% 3.16/1.01      inference(demodulation,[status(thm)],[c_1962,c_929]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_9,plain,
% 3.16/1.01      ( ~ r2_hidden(X0,X1)
% 3.16/1.01      | r2_hidden(X2,k10_relat_1(X3,X1))
% 3.16/1.01      | ~ r2_hidden(X0,k2_relat_1(X3))
% 3.16/1.01      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 3.16/1.01      | ~ v1_relat_1(X3) ),
% 3.16/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_937,plain,
% 3.16/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.16/1.01      | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
% 3.16/1.01      | r2_hidden(X0,k2_relat_1(X3)) != iProver_top
% 3.16/1.01      | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
% 3.16/1.01      | v1_relat_1(X3) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_7,plain,
% 3.16/1.01      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 3.16/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_939,plain,
% 3.16/1.01      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 3.16/1.01      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1046,plain,
% 3.16/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.16/1.01      | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
% 3.16/1.01      | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
% 3.16/1.01      | v1_relat_1(X3) != iProver_top ),
% 3.16/1.01      inference(forward_subsumption_resolution,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_937,c_939]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3281,plain,
% 3.16/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.16/1.01      | r2_hidden(X2,k10_relat_1(k2_zfmisc_1(sK4,sK6),X1)) = iProver_top
% 3.16/1.01      | r2_hidden(k4_tarski(X2,X0),sK7) != iProver_top
% 3.16/1.01      | v1_relat_1(k2_zfmisc_1(sK4,sK6)) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_1978,c_1046]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3477,plain,
% 3.16/1.01      ( r2_hidden(sK9,X0) != iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(k2_zfmisc_1(sK4,sK6),X0)) = iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top
% 3.16/1.01      | v1_relat_1(k2_zfmisc_1(sK4,sK6)) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_2207,c_3281]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_16,negated_conjecture,
% 3.16/1.01      ( r2_hidden(sK9,sK5)
% 3.16/1.01      | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) ),
% 3.16/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_930,plain,
% 3.16/1.01      ( r2_hidden(sK9,sK5) = iProver_top
% 3.16/1.01      | r2_hidden(sK8,k8_relset_1(sK4,sK6,sK7,sK5)) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2208,plain,
% 3.16/1.01      ( r2_hidden(sK9,sK5) = iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
% 3.16/1.01      inference(demodulation,[status(thm)],[c_1962,c_930]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3280,plain,
% 3.16/1.01      ( r2_hidden(sK9,X0) != iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,X0)) = iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top
% 3.16/1.01      | v1_relat_1(sK7) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_2207,c_1046]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3912,plain,
% 3.16/1.01      ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,X0)) = iProver_top
% 3.16/1.01      | r2_hidden(sK9,X0) != iProver_top ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_3280,c_21,c_1101]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3913,plain,
% 3.16/1.01      ( r2_hidden(sK9,X0) != iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,X0)) = iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
% 3.16/1.01      inference(renaming,[status(thm)],[c_3912]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3923,plain,
% 3.16/1.01      ( r2_hidden(sK9,sK5) != iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top
% 3.16/1.01      | iProver_top != iProver_top ),
% 3.16/1.01      inference(equality_factoring,[status(thm)],[c_3913]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3925,plain,
% 3.16/1.01      ( r2_hidden(sK9,sK5) != iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
% 3.16/1.01      inference(equality_resolution_simp,[status(thm)],[c_3923]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3965,plain,
% 3.16/1.01      ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) = iProver_top ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_3477,c_2208,c_3925]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2210,plain,
% 3.16/1.01      ( m1_subset_1(X0,sK6) != iProver_top
% 3.16/1.01      | r2_hidden(X0,sK5) != iProver_top
% 3.16/1.01      | r2_hidden(k4_tarski(sK8,X0),sK7) != iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top ),
% 3.16/1.01      inference(demodulation,[status(thm)],[c_1962,c_931]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2796,plain,
% 3.16/1.01      ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
% 3.16/1.01      | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top
% 3.16/1.01      | v1_relat_1(sK7) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_935,c_2210]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3255,plain,
% 3.16/1.01      ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
% 3.16/1.01      | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 3.16/1.01      | m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_2796,c_21,c_1101]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3256,plain,
% 3.16/1.01      ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
% 3.16/1.01      | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top ),
% 3.16/1.01      inference(renaming,[status(thm)],[c_3255]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_5525,plain,
% 3.16/1.01      ( r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_4287,c_3256]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_6306,plain,
% 3.16/1.01      ( r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 3.16/1.01      | r2_hidden(sK8,k10_relat_1(sK7,X0)) != iProver_top ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_5527,c_2208,c_3925,c_5525]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_6314,plain,
% 3.16/1.01      ( r2_hidden(sK8,k10_relat_1(sK7,sK5)) != iProver_top
% 3.16/1.01      | v1_relat_1(sK7) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_936,c_6306]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(contradiction,plain,
% 3.16/1.01      ( $false ),
% 3.16/1.01      inference(minisat,[status(thm)],[c_6314,c_3965,c_1101,c_21]) ).
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.16/1.01  
% 3.16/1.01  ------                               Statistics
% 3.16/1.01  
% 3.16/1.01  ------ General
% 3.16/1.01  
% 3.16/1.01  abstr_ref_over_cycles:                  0
% 3.16/1.01  abstr_ref_under_cycles:                 0
% 3.16/1.01  gc_basic_clause_elim:                   0
% 3.16/1.01  forced_gc_time:                         0
% 3.16/1.01  parsing_time:                           0.006
% 3.16/1.01  unif_index_cands_time:                  0.
% 3.16/1.01  unif_index_add_time:                    0.
% 3.16/1.01  orderings_time:                         0.
% 3.16/1.01  out_proof_time:                         0.011
% 3.16/1.01  total_time:                             0.191
% 3.16/1.01  num_of_symbols:                         50
% 3.16/1.01  num_of_terms:                           7967
% 3.16/1.01  
% 3.16/1.01  ------ Preprocessing
% 3.16/1.01  
% 3.16/1.01  num_of_splits:                          0
% 3.16/1.01  num_of_split_atoms:                     0
% 3.16/1.01  num_of_reused_defs:                     0
% 3.16/1.01  num_eq_ax_congr_red:                    26
% 3.16/1.01  num_of_sem_filtered_clauses:            1
% 3.16/1.01  num_of_subtypes:                        0
% 3.16/1.01  monotx_restored_types:                  0
% 3.16/1.01  sat_num_of_epr_types:                   0
% 3.16/1.01  sat_num_of_non_cyclic_types:            0
% 3.16/1.01  sat_guarded_non_collapsed_types:        0
% 3.16/1.01  num_pure_diseq_elim:                    0
% 3.16/1.01  simp_replaced_by:                       0
% 3.16/1.01  res_preprocessed:                       80
% 3.16/1.01  prep_upred:                             0
% 3.16/1.01  prep_unflattend:                        24
% 3.16/1.01  smt_new_axioms:                         0
% 3.16/1.01  pred_elim_cands:                        3
% 3.16/1.01  pred_elim:                              0
% 3.16/1.01  pred_elim_cl:                           0
% 3.16/1.01  pred_elim_cycles:                       2
% 3.16/1.01  merged_defs:                            0
% 3.16/1.01  merged_defs_ncl:                        0
% 3.16/1.01  bin_hyper_res:                          0
% 3.16/1.01  prep_cycles:                            3
% 3.16/1.01  pred_elim_time:                         0.004
% 3.16/1.01  splitting_time:                         0.
% 3.16/1.01  sem_filter_time:                        0.
% 3.16/1.01  monotx_time:                            0.
% 3.16/1.01  subtype_inf_time:                       0.
% 3.16/1.01  
% 3.16/1.01  ------ Problem properties
% 3.16/1.01  
% 3.16/1.01  clauses:                                21
% 3.16/1.01  conjectures:                            6
% 3.16/1.01  epr:                                    2
% 3.16/1.01  horn:                                   17
% 3.16/1.01  ground:                                 5
% 3.16/1.01  unary:                                  2
% 3.16/1.01  binary:                                 10
% 3.16/1.01  lits:                                   52
% 3.16/1.01  lits_eq:                                3
% 3.16/1.01  fd_pure:                                0
% 3.16/1.01  fd_pseudo:                              0
% 3.16/1.01  fd_cond:                                0
% 3.16/1.01  fd_pseudo_cond:                         2
% 3.16/1.01  ac_symbols:                             0
% 3.16/1.01  
% 3.16/1.01  ------ Propositional Solver
% 3.16/1.01  
% 3.16/1.01  prop_solver_calls:                      24
% 3.16/1.01  prop_fast_solver_calls:                 714
% 3.16/1.01  smt_solver_calls:                       0
% 3.16/1.01  smt_fast_solver_calls:                  0
% 3.16/1.01  prop_num_of_clauses:                    2886
% 3.16/1.01  prop_preprocess_simplified:             5510
% 3.16/1.01  prop_fo_subsumed:                       15
% 3.16/1.01  prop_solver_time:                       0.
% 3.16/1.01  smt_solver_time:                        0.
% 3.16/1.01  smt_fast_solver_time:                   0.
% 3.16/1.01  prop_fast_solver_time:                  0.
% 3.16/1.01  prop_unsat_core_time:                   0.
% 3.16/1.01  
% 3.16/1.01  ------ QBF
% 3.16/1.01  
% 3.16/1.01  qbf_q_res:                              0
% 3.16/1.01  qbf_num_tautologies:                    0
% 3.16/1.01  qbf_prep_cycles:                        0
% 3.16/1.01  
% 3.16/1.01  ------ BMC1
% 3.16/1.01  
% 3.16/1.01  bmc1_current_bound:                     -1
% 3.16/1.01  bmc1_last_solved_bound:                 -1
% 3.16/1.01  bmc1_unsat_core_size:                   -1
% 3.16/1.01  bmc1_unsat_core_parents_size:           -1
% 3.16/1.01  bmc1_merge_next_fun:                    0
% 3.16/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.16/1.01  
% 3.16/1.01  ------ Instantiation
% 3.16/1.01  
% 3.16/1.01  inst_num_of_clauses:                    743
% 3.16/1.01  inst_num_in_passive:                    301
% 3.16/1.01  inst_num_in_active:                     260
% 3.16/1.01  inst_num_in_unprocessed:                183
% 3.16/1.01  inst_num_of_loops:                      400
% 3.16/1.01  inst_num_of_learning_restarts:          0
% 3.16/1.01  inst_num_moves_active_passive:          136
% 3.16/1.01  inst_lit_activity:                      0
% 3.16/1.01  inst_lit_activity_moves:                0
% 3.16/1.01  inst_num_tautologies:                   0
% 3.16/1.01  inst_num_prop_implied:                  0
% 3.16/1.01  inst_num_existing_simplified:           0
% 3.16/1.01  inst_num_eq_res_simplified:             0
% 3.16/1.01  inst_num_child_elim:                    0
% 3.16/1.01  inst_num_of_dismatching_blockings:      52
% 3.16/1.01  inst_num_of_non_proper_insts:           466
% 3.16/1.01  inst_num_of_duplicates:                 0
% 3.16/1.01  inst_inst_num_from_inst_to_res:         0
% 3.16/1.01  inst_dismatching_checking_time:         0.
% 3.16/1.01  
% 3.16/1.01  ------ Resolution
% 3.16/1.01  
% 3.16/1.01  res_num_of_clauses:                     0
% 3.16/1.01  res_num_in_passive:                     0
% 3.16/1.01  res_num_in_active:                      0
% 3.16/1.01  res_num_of_loops:                       83
% 3.16/1.01  res_forward_subset_subsumed:            19
% 3.16/1.01  res_backward_subset_subsumed:           2
% 3.16/1.01  res_forward_subsumed:                   0
% 3.16/1.01  res_backward_subsumed:                  0
% 3.16/1.01  res_forward_subsumption_resolution:     1
% 3.16/1.01  res_backward_subsumption_resolution:    0
% 3.16/1.01  res_clause_to_clause_subsumption:       395
% 3.16/1.01  res_orphan_elimination:                 0
% 3.16/1.01  res_tautology_del:                      25
% 3.16/1.01  res_num_eq_res_simplified:              0
% 3.16/1.01  res_num_sel_changes:                    0
% 3.16/1.01  res_moves_from_active_to_pass:          0
% 3.16/1.01  
% 3.16/1.01  ------ Superposition
% 3.16/1.01  
% 3.16/1.01  sup_time_total:                         0.
% 3.16/1.01  sup_time_generating:                    0.
% 3.16/1.01  sup_time_sim_full:                      0.
% 3.16/1.01  sup_time_sim_immed:                     0.
% 3.16/1.01  
% 3.16/1.01  sup_num_of_clauses:                     159
% 3.16/1.01  sup_num_in_active:                      68
% 3.16/1.01  sup_num_in_passive:                     91
% 3.16/1.01  sup_num_of_loops:                       78
% 3.16/1.01  sup_fw_superposition:                   80
% 3.16/1.01  sup_bw_superposition:                   89
% 3.16/1.01  sup_immediate_simplified:               9
% 3.16/1.01  sup_given_eliminated:                   0
% 3.16/1.01  comparisons_done:                       0
% 3.16/1.01  comparisons_avoided:                    0
% 3.16/1.01  
% 3.16/1.01  ------ Simplifications
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  sim_fw_subset_subsumed:                 1
% 3.16/1.01  sim_bw_subset_subsumed:                 8
% 3.16/1.01  sim_fw_subsumed:                        2
% 3.16/1.01  sim_bw_subsumed:                        2
% 3.16/1.01  sim_fw_subsumption_res:                 2
% 3.16/1.01  sim_bw_subsumption_res:                 3
% 3.16/1.01  sim_tautology_del:                      7
% 3.16/1.01  sim_eq_tautology_del:                   0
% 3.16/1.01  sim_eq_res_simp:                        1
% 3.16/1.01  sim_fw_demodulated:                     0
% 3.16/1.01  sim_bw_demodulated:                     7
% 3.16/1.01  sim_light_normalised:                   0
% 3.16/1.01  sim_joinable_taut:                      0
% 3.16/1.01  sim_joinable_simp:                      0
% 3.16/1.01  sim_ac_normalised:                      0
% 3.16/1.01  sim_smt_subsumption:                    0
% 3.16/1.01  
%------------------------------------------------------------------------------

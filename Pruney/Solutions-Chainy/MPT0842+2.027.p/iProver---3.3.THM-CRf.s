%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:07 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  132 (1586 expanded)
%              Number of clauses        :   84 ( 461 expanded)
%              Number of leaves         :   13 ( 366 expanded)
%              Depth                    :   22
%              Number of atoms          :  460 (10119 expanded)
%              Number of equality atoms :  156 ( 601 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK0(X0,X1,X2)),X2)
        & r2_hidden(sK0(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK0(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f11,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X4,X2,X3,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X4,X6),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK6,X1)
        & r2_hidden(k4_tarski(X4,sK6),X3)
        & m1_subset_1(sK6,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f32,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f28,f31,f30,f29])).

fof(f48,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK4)
    | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(k4_tarski(sK5,X5),sK4)
      | ~ m1_subset_1(X5,sK3)
      | ~ r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,
    ( r2_hidden(sK6,sK2)
    | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,
    ( m1_subset_1(sK6,sK3)
    | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK0(X0,X2,X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_536,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK0(X0,X2,X1)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(k4_tarski(sK5,sK6),sK4)
    | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_527,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK4) = iProver_top
    | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(k4_tarski(sK5,X0),sK4)
    | ~ r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2))
    | ~ m1_subset_1(X0,sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_529,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k4_tarski(sK5,X0),sK4) != iProver_top
    | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_775,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k4_tarski(sK5,X0),sK4) != iProver_top
    | r2_hidden(k4_tarski(sK5,sK6),sK4) = iProver_top
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_527,c_529])).

cnf(c_1765,plain,
    ( r2_hidden(sK0(sK5,X0,sK4),sK2) != iProver_top
    | r2_hidden(k4_tarski(sK5,sK6),sK4) = iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,X0)) != iProver_top
    | m1_subset_1(sK0(sK5,X0,sK4),sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_536,c_775])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_18,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_21,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK4) = iProver_top
    | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_673,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_902,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK3))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_903,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_902])).

cnf(c_524,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_531,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_919,plain,
    ( k2_relset_1(sK1,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_524,c_531])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_532,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1087,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_919,c_532])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1138,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1139,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1138])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_530,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_897,plain,
    ( k8_relset_1(sK1,sK3,sK4,X0) = k10_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_524,c_530])).

cnf(c_1149,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK4) = iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_897,c_527])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_932,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
    | r2_hidden(sK0(X0,X1,sK4),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1716,plain,
    ( r2_hidden(sK0(sK5,sK2,sK4),k2_relat_1(sK4))
    | ~ r2_hidden(sK5,k10_relat_1(sK4,sK2))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_932])).

cnf(c_1717,plain,
    ( r2_hidden(sK0(sK5,sK2,sK4),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1716])).

cnf(c_931,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
    | r2_hidden(k4_tarski(X0,sK0(X0,X1,sK4)),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1715,plain,
    ( r2_hidden(k4_tarski(sK5,sK0(sK5,sK2,sK4)),sK4)
    | ~ r2_hidden(sK5,k10_relat_1(sK4,sK2))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_931])).

cnf(c_1719,plain,
    ( r2_hidden(k4_tarski(sK5,sK0(sK5,sK2,sK4)),sK4) = iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1715])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_933,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
    | r2_hidden(sK0(X0,X1,sK4),X1)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1714,plain,
    ( r2_hidden(sK0(sK5,sK2,sK4),sK2)
    | ~ r2_hidden(sK5,k10_relat_1(sK4,sK2))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_933])).

cnf(c_1721,plain,
    ( r2_hidden(sK0(sK5,sK2,sK4),sK2) = iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1714])).

cnf(c_2091,plain,
    ( ~ r2_hidden(sK0(sK5,sK2,sK4),sK2)
    | ~ r2_hidden(k4_tarski(sK5,sK0(sK5,sK2,sK4)),sK4)
    | ~ r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2))
    | ~ m1_subset_1(sK0(sK5,sK2,sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2092,plain,
    ( r2_hidden(sK0(sK5,sK2,sK4),sK2) != iProver_top
    | r2_hidden(k4_tarski(sK5,sK0(sK5,sK2,sK4)),sK4) != iProver_top
    | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) != iProver_top
    | m1_subset_1(sK0(sK5,sK2,sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2091])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2138,plain,
    ( ~ r2_hidden(sK0(sK5,sK2,sK4),k2_relat_1(sK4))
    | m1_subset_1(sK0(sK5,sK2,sK4),X0)
    | ~ m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2139,plain,
    ( r2_hidden(sK0(sK5,sK2,sK4),k2_relat_1(sK4)) != iProver_top
    | m1_subset_1(sK0(sK5,sK2,sK4),X0) = iProver_top
    | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2138])).

cnf(c_2141,plain,
    ( r2_hidden(sK0(sK5,sK2,sK4),k2_relat_1(sK4)) != iProver_top
    | m1_subset_1(sK0(sK5,sK2,sK4),sK3) = iProver_top
    | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2139])).

cnf(c_2240,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1765,c_18,c_21,c_903,c_1087,c_1139,c_1149,c_1717,c_1719,c_1721,c_2092,c_2141])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_538,plain,
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
    inference(cnf_transformation,[],[f41])).

cnf(c_534,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_627,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_538,c_534])).

cnf(c_2440,plain,
    ( r2_hidden(sK6,X0) != iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,X0)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2240,c_627])).

cnf(c_2537,plain,
    ( r2_hidden(sK5,k10_relat_1(sK4,X0)) = iProver_top
    | r2_hidden(sK6,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2440,c_18,c_903,c_1139])).

cnf(c_2538,plain,
    ( r2_hidden(sK6,X0) != iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2537])).

cnf(c_1152,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k4_tarski(sK5,X0),sK4) != iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_897,c_529])).

cnf(c_2247,plain,
    ( r2_hidden(sK6,sK2) != iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
    | m1_subset_1(sK6,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2240,c_1152])).

cnf(c_537,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK6,sK2)
    | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_528,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_768,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k4_tarski(sK5,X0),sK4) != iProver_top
    | r2_hidden(sK6,sK2) = iProver_top
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_528,c_529])).

cnf(c_1766,plain,
    ( r2_hidden(sK0(sK5,X0,sK4),sK2) != iProver_top
    | r2_hidden(sK6,sK2) = iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,X0)) != iProver_top
    | m1_subset_1(sK0(sK5,X0,sK4),sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_536,c_768])).

cnf(c_2099,plain,
    ( m1_subset_1(sK0(sK5,X0,sK4),sK3) != iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,X0)) != iProver_top
    | r2_hidden(sK6,sK2) = iProver_top
    | r2_hidden(sK0(sK5,X0,sK4),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1766,c_18,c_903,c_1139])).

cnf(c_2100,plain,
    ( r2_hidden(sK0(sK5,X0,sK4),sK2) != iProver_top
    | r2_hidden(sK6,sK2) = iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,X0)) != iProver_top
    | m1_subset_1(sK0(sK5,X0,sK4),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2099])).

cnf(c_535,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1463,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1087,c_18])).

cnf(c_541,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1468,plain,
    ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
    | m1_subset_1(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1463,c_541])).

cnf(c_1592,plain,
    ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
    | m1_subset_1(sK0(X0,X1,sK4),sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_535,c_1468])).

cnf(c_1669,plain,
    ( m1_subset_1(sK0(X0,X1,sK4),sK3) = iProver_top
    | r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1592,c_18,c_903,c_1139])).

cnf(c_1670,plain,
    ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
    | m1_subset_1(sK0(X0,X1,sK4),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_1669])).

cnf(c_2109,plain,
    ( r2_hidden(sK0(sK5,X0,sK4),sK2) != iProver_top
    | r2_hidden(sK6,sK2) = iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2100,c_1670])).

cnf(c_2113,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_537,c_2109])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2))
    | m1_subset_1(sK6,sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_526,plain,
    ( r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) = iProver_top
    | m1_subset_1(sK6,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_736,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k4_tarski(sK5,X0),sK4) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(sK6,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_526,c_529])).

cnf(c_1767,plain,
    ( r2_hidden(sK0(sK5,X0,sK4),sK2) != iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,X0)) != iProver_top
    | m1_subset_1(sK0(sK5,X0,sK4),sK3) != iProver_top
    | m1_subset_1(sK6,sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_536,c_736])).

cnf(c_20,plain,
    ( r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) = iProver_top
    | m1_subset_1(sK6,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1151,plain,
    ( r2_hidden(sK5,k10_relat_1(sK4,sK2)) = iProver_top
    | m1_subset_1(sK6,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_897,c_526])).

cnf(c_2234,plain,
    ( m1_subset_1(sK6,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1767,c_18,c_20,c_903,c_1087,c_1139,c_1151,c_1717,c_1719,c_1721,c_2092,c_2141])).

cnf(c_2299,plain,
    ( r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2247,c_18,c_20,c_903,c_1087,c_1139,c_1151,c_1717,c_1719,c_1721,c_2092,c_2113,c_2141])).

cnf(c_2546,plain,
    ( r2_hidden(sK6,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2538,c_2299])).

cnf(c_1150,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | r2_hidden(sK5,k10_relat_1(sK4,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_897,c_528])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2546,c_2299,c_1150])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.73/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/0.99  
% 1.73/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.73/0.99  
% 1.73/0.99  ------  iProver source info
% 1.73/0.99  
% 1.73/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.73/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.73/0.99  git: non_committed_changes: false
% 1.73/0.99  git: last_make_outside_of_git: false
% 1.73/0.99  
% 1.73/0.99  ------ 
% 1.73/0.99  
% 1.73/0.99  ------ Input Options
% 1.73/0.99  
% 1.73/0.99  --out_options                           all
% 1.73/0.99  --tptp_safe_out                         true
% 1.73/0.99  --problem_path                          ""
% 1.73/0.99  --include_path                          ""
% 1.73/0.99  --clausifier                            res/vclausify_rel
% 1.73/0.99  --clausifier_options                    --mode clausify
% 1.73/0.99  --stdin                                 false
% 1.73/0.99  --stats_out                             all
% 1.73/0.99  
% 1.73/0.99  ------ General Options
% 1.73/0.99  
% 1.73/0.99  --fof                                   false
% 1.73/0.99  --time_out_real                         305.
% 1.73/0.99  --time_out_virtual                      -1.
% 1.73/0.99  --symbol_type_check                     false
% 1.73/0.99  --clausify_out                          false
% 1.73/0.99  --sig_cnt_out                           false
% 1.73/0.99  --trig_cnt_out                          false
% 1.73/0.99  --trig_cnt_out_tolerance                1.
% 1.73/0.99  --trig_cnt_out_sk_spl                   false
% 1.73/0.99  --abstr_cl_out                          false
% 1.73/0.99  
% 1.73/0.99  ------ Global Options
% 1.73/0.99  
% 1.73/0.99  --schedule                              default
% 1.73/0.99  --add_important_lit                     false
% 1.73/0.99  --prop_solver_per_cl                    1000
% 1.73/0.99  --min_unsat_core                        false
% 1.73/0.99  --soft_assumptions                      false
% 1.73/0.99  --soft_lemma_size                       3
% 1.73/0.99  --prop_impl_unit_size                   0
% 1.73/0.99  --prop_impl_unit                        []
% 1.73/0.99  --share_sel_clauses                     true
% 1.73/0.99  --reset_solvers                         false
% 1.73/0.99  --bc_imp_inh                            [conj_cone]
% 1.73/0.99  --conj_cone_tolerance                   3.
% 1.73/0.99  --extra_neg_conj                        none
% 1.73/0.99  --large_theory_mode                     true
% 1.73/0.99  --prolific_symb_bound                   200
% 1.73/0.99  --lt_threshold                          2000
% 1.73/0.99  --clause_weak_htbl                      true
% 1.73/0.99  --gc_record_bc_elim                     false
% 1.73/0.99  
% 1.73/0.99  ------ Preprocessing Options
% 1.73/0.99  
% 1.73/0.99  --preprocessing_flag                    true
% 1.73/0.99  --time_out_prep_mult                    0.1
% 1.73/0.99  --splitting_mode                        input
% 1.73/0.99  --splitting_grd                         true
% 1.73/0.99  --splitting_cvd                         false
% 1.73/0.99  --splitting_cvd_svl                     false
% 1.73/0.99  --splitting_nvd                         32
% 1.73/0.99  --sub_typing                            true
% 1.73/0.99  --prep_gs_sim                           true
% 1.73/0.99  --prep_unflatten                        true
% 1.73/0.99  --prep_res_sim                          true
% 1.73/0.99  --prep_upred                            true
% 1.73/0.99  --prep_sem_filter                       exhaustive
% 1.73/0.99  --prep_sem_filter_out                   false
% 1.73/0.99  --pred_elim                             true
% 1.73/0.99  --res_sim_input                         true
% 1.73/0.99  --eq_ax_congr_red                       true
% 1.73/0.99  --pure_diseq_elim                       true
% 1.73/0.99  --brand_transform                       false
% 1.73/0.99  --non_eq_to_eq                          false
% 1.73/0.99  --prep_def_merge                        true
% 1.73/0.99  --prep_def_merge_prop_impl              false
% 1.73/0.99  --prep_def_merge_mbd                    true
% 1.73/0.99  --prep_def_merge_tr_red                 false
% 1.73/0.99  --prep_def_merge_tr_cl                  false
% 1.73/0.99  --smt_preprocessing                     true
% 1.73/0.99  --smt_ac_axioms                         fast
% 1.73/0.99  --preprocessed_out                      false
% 1.73/0.99  --preprocessed_stats                    false
% 1.73/0.99  
% 1.73/0.99  ------ Abstraction refinement Options
% 1.73/0.99  
% 1.73/0.99  --abstr_ref                             []
% 1.73/0.99  --abstr_ref_prep                        false
% 1.73/0.99  --abstr_ref_until_sat                   false
% 1.73/0.99  --abstr_ref_sig_restrict                funpre
% 1.73/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.73/0.99  --abstr_ref_under                       []
% 1.73/0.99  
% 1.73/0.99  ------ SAT Options
% 1.73/0.99  
% 1.73/0.99  --sat_mode                              false
% 1.73/0.99  --sat_fm_restart_options                ""
% 1.73/0.99  --sat_gr_def                            false
% 1.73/0.99  --sat_epr_types                         true
% 1.73/0.99  --sat_non_cyclic_types                  false
% 1.73/0.99  --sat_finite_models                     false
% 1.73/0.99  --sat_fm_lemmas                         false
% 1.73/0.99  --sat_fm_prep                           false
% 1.73/0.99  --sat_fm_uc_incr                        true
% 1.73/0.99  --sat_out_model                         small
% 1.73/0.99  --sat_out_clauses                       false
% 1.73/0.99  
% 1.73/0.99  ------ QBF Options
% 1.73/0.99  
% 1.73/0.99  --qbf_mode                              false
% 1.73/0.99  --qbf_elim_univ                         false
% 1.73/0.99  --qbf_dom_inst                          none
% 1.73/0.99  --qbf_dom_pre_inst                      false
% 1.73/0.99  --qbf_sk_in                             false
% 1.73/0.99  --qbf_pred_elim                         true
% 1.73/0.99  --qbf_split                             512
% 1.73/0.99  
% 1.73/0.99  ------ BMC1 Options
% 1.73/0.99  
% 1.73/0.99  --bmc1_incremental                      false
% 1.73/0.99  --bmc1_axioms                           reachable_all
% 1.73/0.99  --bmc1_min_bound                        0
% 1.73/0.99  --bmc1_max_bound                        -1
% 1.73/0.99  --bmc1_max_bound_default                -1
% 1.73/0.99  --bmc1_symbol_reachability              true
% 1.73/0.99  --bmc1_property_lemmas                  false
% 1.73/0.99  --bmc1_k_induction                      false
% 1.73/0.99  --bmc1_non_equiv_states                 false
% 1.73/0.99  --bmc1_deadlock                         false
% 1.73/0.99  --bmc1_ucm                              false
% 1.73/0.99  --bmc1_add_unsat_core                   none
% 1.73/1.00  --bmc1_unsat_core_children              false
% 1.73/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.73/1.00  --bmc1_out_stat                         full
% 1.73/1.00  --bmc1_ground_init                      false
% 1.73/1.00  --bmc1_pre_inst_next_state              false
% 1.73/1.00  --bmc1_pre_inst_state                   false
% 1.73/1.00  --bmc1_pre_inst_reach_state             false
% 1.73/1.00  --bmc1_out_unsat_core                   false
% 1.73/1.00  --bmc1_aig_witness_out                  false
% 1.73/1.00  --bmc1_verbose                          false
% 1.73/1.00  --bmc1_dump_clauses_tptp                false
% 1.73/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.73/1.00  --bmc1_dump_file                        -
% 1.73/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.73/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.73/1.00  --bmc1_ucm_extend_mode                  1
% 1.73/1.00  --bmc1_ucm_init_mode                    2
% 1.73/1.00  --bmc1_ucm_cone_mode                    none
% 1.73/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.73/1.00  --bmc1_ucm_relax_model                  4
% 1.73/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.73/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.73/1.00  --bmc1_ucm_layered_model                none
% 1.73/1.00  --bmc1_ucm_max_lemma_size               10
% 1.73/1.00  
% 1.73/1.00  ------ AIG Options
% 1.73/1.00  
% 1.73/1.00  --aig_mode                              false
% 1.73/1.00  
% 1.73/1.00  ------ Instantiation Options
% 1.73/1.00  
% 1.73/1.00  --instantiation_flag                    true
% 1.73/1.00  --inst_sos_flag                         false
% 1.73/1.00  --inst_sos_phase                        true
% 1.73/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.73/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.73/1.00  --inst_lit_sel_side                     num_symb
% 1.73/1.00  --inst_solver_per_active                1400
% 1.73/1.00  --inst_solver_calls_frac                1.
% 1.73/1.00  --inst_passive_queue_type               priority_queues
% 1.73/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.73/1.00  --inst_passive_queues_freq              [25;2]
% 1.73/1.00  --inst_dismatching                      true
% 1.73/1.00  --inst_eager_unprocessed_to_passive     true
% 1.73/1.00  --inst_prop_sim_given                   true
% 1.73/1.00  --inst_prop_sim_new                     false
% 1.73/1.00  --inst_subs_new                         false
% 1.73/1.00  --inst_eq_res_simp                      false
% 1.73/1.00  --inst_subs_given                       false
% 1.73/1.00  --inst_orphan_elimination               true
% 1.73/1.00  --inst_learning_loop_flag               true
% 1.73/1.00  --inst_learning_start                   3000
% 1.73/1.00  --inst_learning_factor                  2
% 1.73/1.00  --inst_start_prop_sim_after_learn       3
% 1.73/1.00  --inst_sel_renew                        solver
% 1.73/1.00  --inst_lit_activity_flag                true
% 1.73/1.00  --inst_restr_to_given                   false
% 1.73/1.00  --inst_activity_threshold               500
% 1.73/1.00  --inst_out_proof                        true
% 1.73/1.00  
% 1.73/1.00  ------ Resolution Options
% 1.73/1.00  
% 1.73/1.00  --resolution_flag                       true
% 1.73/1.00  --res_lit_sel                           adaptive
% 1.73/1.00  --res_lit_sel_side                      none
% 1.73/1.00  --res_ordering                          kbo
% 1.73/1.00  --res_to_prop_solver                    active
% 1.73/1.00  --res_prop_simpl_new                    false
% 1.73/1.00  --res_prop_simpl_given                  true
% 1.73/1.00  --res_passive_queue_type                priority_queues
% 1.73/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.73/1.00  --res_passive_queues_freq               [15;5]
% 1.73/1.00  --res_forward_subs                      full
% 1.73/1.00  --res_backward_subs                     full
% 1.73/1.00  --res_forward_subs_resolution           true
% 1.73/1.00  --res_backward_subs_resolution          true
% 1.73/1.00  --res_orphan_elimination                true
% 1.73/1.00  --res_time_limit                        2.
% 1.73/1.00  --res_out_proof                         true
% 1.73/1.00  
% 1.73/1.00  ------ Superposition Options
% 1.73/1.00  
% 1.73/1.00  --superposition_flag                    true
% 1.73/1.00  --sup_passive_queue_type                priority_queues
% 1.73/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.73/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.73/1.00  --demod_completeness_check              fast
% 1.73/1.00  --demod_use_ground                      true
% 1.73/1.00  --sup_to_prop_solver                    passive
% 1.73/1.00  --sup_prop_simpl_new                    true
% 1.73/1.00  --sup_prop_simpl_given                  true
% 1.73/1.00  --sup_fun_splitting                     false
% 1.73/1.00  --sup_smt_interval                      50000
% 1.73/1.00  
% 1.73/1.00  ------ Superposition Simplification Setup
% 1.73/1.00  
% 1.73/1.00  --sup_indices_passive                   []
% 1.73/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.73/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.00  --sup_full_bw                           [BwDemod]
% 1.73/1.00  --sup_immed_triv                        [TrivRules]
% 1.73/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.73/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.00  --sup_immed_bw_main                     []
% 1.73/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.73/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/1.00  
% 1.73/1.00  ------ Combination Options
% 1.73/1.00  
% 1.73/1.00  --comb_res_mult                         3
% 1.73/1.00  --comb_sup_mult                         2
% 1.73/1.00  --comb_inst_mult                        10
% 1.73/1.00  
% 1.73/1.00  ------ Debug Options
% 1.73/1.00  
% 1.73/1.00  --dbg_backtrace                         false
% 1.73/1.00  --dbg_dump_prop_clauses                 false
% 1.73/1.00  --dbg_dump_prop_clauses_file            -
% 1.73/1.00  --dbg_out_stat                          false
% 1.73/1.00  ------ Parsing...
% 1.73/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.73/1.00  
% 1.73/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.73/1.00  
% 1.73/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.73/1.00  
% 1.73/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.73/1.00  ------ Proving...
% 1.73/1.00  ------ Problem Properties 
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  clauses                                 18
% 1.73/1.00  conjectures                             6
% 1.73/1.00  EPR                                     1
% 1.73/1.00  Horn                                    15
% 1.73/1.00  unary                                   3
% 1.73/1.00  binary                                  6
% 1.73/1.00  lits                                    45
% 1.73/1.00  lits eq                                 2
% 1.73/1.00  fd_pure                                 0
% 1.73/1.00  fd_pseudo                               0
% 1.73/1.00  fd_cond                                 0
% 1.73/1.00  fd_pseudo_cond                          0
% 1.73/1.00  AC symbols                              0
% 1.73/1.00  
% 1.73/1.00  ------ Schedule dynamic 5 is on 
% 1.73/1.00  
% 1.73/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  ------ 
% 1.73/1.00  Current options:
% 1.73/1.00  ------ 
% 1.73/1.00  
% 1.73/1.00  ------ Input Options
% 1.73/1.00  
% 1.73/1.00  --out_options                           all
% 1.73/1.00  --tptp_safe_out                         true
% 1.73/1.00  --problem_path                          ""
% 1.73/1.00  --include_path                          ""
% 1.73/1.00  --clausifier                            res/vclausify_rel
% 1.73/1.00  --clausifier_options                    --mode clausify
% 1.73/1.00  --stdin                                 false
% 1.73/1.00  --stats_out                             all
% 1.73/1.00  
% 1.73/1.00  ------ General Options
% 1.73/1.00  
% 1.73/1.00  --fof                                   false
% 1.73/1.00  --time_out_real                         305.
% 1.73/1.00  --time_out_virtual                      -1.
% 1.73/1.00  --symbol_type_check                     false
% 1.73/1.00  --clausify_out                          false
% 1.73/1.00  --sig_cnt_out                           false
% 1.73/1.00  --trig_cnt_out                          false
% 1.73/1.00  --trig_cnt_out_tolerance                1.
% 1.73/1.00  --trig_cnt_out_sk_spl                   false
% 1.73/1.00  --abstr_cl_out                          false
% 1.73/1.00  
% 1.73/1.00  ------ Global Options
% 1.73/1.00  
% 1.73/1.00  --schedule                              default
% 1.73/1.00  --add_important_lit                     false
% 1.73/1.00  --prop_solver_per_cl                    1000
% 1.73/1.00  --min_unsat_core                        false
% 1.73/1.00  --soft_assumptions                      false
% 1.73/1.00  --soft_lemma_size                       3
% 1.73/1.00  --prop_impl_unit_size                   0
% 1.73/1.00  --prop_impl_unit                        []
% 1.73/1.00  --share_sel_clauses                     true
% 1.73/1.00  --reset_solvers                         false
% 1.73/1.00  --bc_imp_inh                            [conj_cone]
% 1.73/1.00  --conj_cone_tolerance                   3.
% 1.73/1.00  --extra_neg_conj                        none
% 1.73/1.00  --large_theory_mode                     true
% 1.73/1.00  --prolific_symb_bound                   200
% 1.73/1.00  --lt_threshold                          2000
% 1.73/1.00  --clause_weak_htbl                      true
% 1.73/1.00  --gc_record_bc_elim                     false
% 1.73/1.00  
% 1.73/1.00  ------ Preprocessing Options
% 1.73/1.00  
% 1.73/1.00  --preprocessing_flag                    true
% 1.73/1.00  --time_out_prep_mult                    0.1
% 1.73/1.00  --splitting_mode                        input
% 1.73/1.00  --splitting_grd                         true
% 1.73/1.00  --splitting_cvd                         false
% 1.73/1.00  --splitting_cvd_svl                     false
% 1.73/1.00  --splitting_nvd                         32
% 1.73/1.00  --sub_typing                            true
% 1.73/1.00  --prep_gs_sim                           true
% 1.73/1.00  --prep_unflatten                        true
% 1.73/1.00  --prep_res_sim                          true
% 1.73/1.00  --prep_upred                            true
% 1.73/1.00  --prep_sem_filter                       exhaustive
% 1.73/1.00  --prep_sem_filter_out                   false
% 1.73/1.00  --pred_elim                             true
% 1.73/1.00  --res_sim_input                         true
% 1.73/1.00  --eq_ax_congr_red                       true
% 1.73/1.00  --pure_diseq_elim                       true
% 1.73/1.00  --brand_transform                       false
% 1.73/1.00  --non_eq_to_eq                          false
% 1.73/1.00  --prep_def_merge                        true
% 1.73/1.00  --prep_def_merge_prop_impl              false
% 1.73/1.00  --prep_def_merge_mbd                    true
% 1.73/1.00  --prep_def_merge_tr_red                 false
% 1.73/1.00  --prep_def_merge_tr_cl                  false
% 1.73/1.00  --smt_preprocessing                     true
% 1.73/1.00  --smt_ac_axioms                         fast
% 1.73/1.00  --preprocessed_out                      false
% 1.73/1.00  --preprocessed_stats                    false
% 1.73/1.00  
% 1.73/1.00  ------ Abstraction refinement Options
% 1.73/1.00  
% 1.73/1.00  --abstr_ref                             []
% 1.73/1.00  --abstr_ref_prep                        false
% 1.73/1.00  --abstr_ref_until_sat                   false
% 1.73/1.00  --abstr_ref_sig_restrict                funpre
% 1.73/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.73/1.00  --abstr_ref_under                       []
% 1.73/1.00  
% 1.73/1.00  ------ SAT Options
% 1.73/1.00  
% 1.73/1.00  --sat_mode                              false
% 1.73/1.00  --sat_fm_restart_options                ""
% 1.73/1.00  --sat_gr_def                            false
% 1.73/1.00  --sat_epr_types                         true
% 1.73/1.00  --sat_non_cyclic_types                  false
% 1.73/1.00  --sat_finite_models                     false
% 1.73/1.00  --sat_fm_lemmas                         false
% 1.73/1.00  --sat_fm_prep                           false
% 1.73/1.00  --sat_fm_uc_incr                        true
% 1.73/1.00  --sat_out_model                         small
% 1.73/1.00  --sat_out_clauses                       false
% 1.73/1.00  
% 1.73/1.00  ------ QBF Options
% 1.73/1.00  
% 1.73/1.00  --qbf_mode                              false
% 1.73/1.00  --qbf_elim_univ                         false
% 1.73/1.00  --qbf_dom_inst                          none
% 1.73/1.00  --qbf_dom_pre_inst                      false
% 1.73/1.00  --qbf_sk_in                             false
% 1.73/1.00  --qbf_pred_elim                         true
% 1.73/1.00  --qbf_split                             512
% 1.73/1.00  
% 1.73/1.00  ------ BMC1 Options
% 1.73/1.00  
% 1.73/1.00  --bmc1_incremental                      false
% 1.73/1.00  --bmc1_axioms                           reachable_all
% 1.73/1.00  --bmc1_min_bound                        0
% 1.73/1.00  --bmc1_max_bound                        -1
% 1.73/1.00  --bmc1_max_bound_default                -1
% 1.73/1.00  --bmc1_symbol_reachability              true
% 1.73/1.00  --bmc1_property_lemmas                  false
% 1.73/1.00  --bmc1_k_induction                      false
% 1.73/1.00  --bmc1_non_equiv_states                 false
% 1.73/1.00  --bmc1_deadlock                         false
% 1.73/1.00  --bmc1_ucm                              false
% 1.73/1.00  --bmc1_add_unsat_core                   none
% 1.73/1.00  --bmc1_unsat_core_children              false
% 1.73/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.73/1.00  --bmc1_out_stat                         full
% 1.73/1.00  --bmc1_ground_init                      false
% 1.73/1.00  --bmc1_pre_inst_next_state              false
% 1.73/1.00  --bmc1_pre_inst_state                   false
% 1.73/1.00  --bmc1_pre_inst_reach_state             false
% 1.73/1.00  --bmc1_out_unsat_core                   false
% 1.73/1.00  --bmc1_aig_witness_out                  false
% 1.73/1.00  --bmc1_verbose                          false
% 1.73/1.00  --bmc1_dump_clauses_tptp                false
% 1.73/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.73/1.00  --bmc1_dump_file                        -
% 1.73/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.73/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.73/1.00  --bmc1_ucm_extend_mode                  1
% 1.73/1.00  --bmc1_ucm_init_mode                    2
% 1.73/1.00  --bmc1_ucm_cone_mode                    none
% 1.73/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.73/1.00  --bmc1_ucm_relax_model                  4
% 1.73/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.73/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.73/1.00  --bmc1_ucm_layered_model                none
% 1.73/1.00  --bmc1_ucm_max_lemma_size               10
% 1.73/1.00  
% 1.73/1.00  ------ AIG Options
% 1.73/1.00  
% 1.73/1.00  --aig_mode                              false
% 1.73/1.00  
% 1.73/1.00  ------ Instantiation Options
% 1.73/1.00  
% 1.73/1.00  --instantiation_flag                    true
% 1.73/1.00  --inst_sos_flag                         false
% 1.73/1.00  --inst_sos_phase                        true
% 1.73/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.73/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.73/1.00  --inst_lit_sel_side                     none
% 1.73/1.00  --inst_solver_per_active                1400
% 1.73/1.00  --inst_solver_calls_frac                1.
% 1.73/1.00  --inst_passive_queue_type               priority_queues
% 1.73/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.73/1.00  --inst_passive_queues_freq              [25;2]
% 1.73/1.00  --inst_dismatching                      true
% 1.73/1.00  --inst_eager_unprocessed_to_passive     true
% 1.73/1.00  --inst_prop_sim_given                   true
% 1.73/1.00  --inst_prop_sim_new                     false
% 1.73/1.00  --inst_subs_new                         false
% 1.73/1.00  --inst_eq_res_simp                      false
% 1.73/1.00  --inst_subs_given                       false
% 1.73/1.00  --inst_orphan_elimination               true
% 1.73/1.00  --inst_learning_loop_flag               true
% 1.73/1.00  --inst_learning_start                   3000
% 1.73/1.00  --inst_learning_factor                  2
% 1.73/1.00  --inst_start_prop_sim_after_learn       3
% 1.73/1.00  --inst_sel_renew                        solver
% 1.73/1.00  --inst_lit_activity_flag                true
% 1.73/1.00  --inst_restr_to_given                   false
% 1.73/1.00  --inst_activity_threshold               500
% 1.73/1.00  --inst_out_proof                        true
% 1.73/1.00  
% 1.73/1.00  ------ Resolution Options
% 1.73/1.00  
% 1.73/1.00  --resolution_flag                       false
% 1.73/1.00  --res_lit_sel                           adaptive
% 1.73/1.00  --res_lit_sel_side                      none
% 1.73/1.00  --res_ordering                          kbo
% 1.73/1.00  --res_to_prop_solver                    active
% 1.73/1.00  --res_prop_simpl_new                    false
% 1.73/1.00  --res_prop_simpl_given                  true
% 1.73/1.00  --res_passive_queue_type                priority_queues
% 1.73/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.73/1.00  --res_passive_queues_freq               [15;5]
% 1.73/1.00  --res_forward_subs                      full
% 1.73/1.00  --res_backward_subs                     full
% 1.73/1.00  --res_forward_subs_resolution           true
% 1.73/1.00  --res_backward_subs_resolution          true
% 1.73/1.00  --res_orphan_elimination                true
% 1.73/1.00  --res_time_limit                        2.
% 1.73/1.00  --res_out_proof                         true
% 1.73/1.00  
% 1.73/1.00  ------ Superposition Options
% 1.73/1.00  
% 1.73/1.00  --superposition_flag                    true
% 1.73/1.00  --sup_passive_queue_type                priority_queues
% 1.73/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.73/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.73/1.00  --demod_completeness_check              fast
% 1.73/1.00  --demod_use_ground                      true
% 1.73/1.00  --sup_to_prop_solver                    passive
% 1.73/1.00  --sup_prop_simpl_new                    true
% 1.73/1.00  --sup_prop_simpl_given                  true
% 1.73/1.00  --sup_fun_splitting                     false
% 1.73/1.00  --sup_smt_interval                      50000
% 1.73/1.00  
% 1.73/1.00  ------ Superposition Simplification Setup
% 1.73/1.00  
% 1.73/1.00  --sup_indices_passive                   []
% 1.73/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.73/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.00  --sup_full_bw                           [BwDemod]
% 1.73/1.00  --sup_immed_triv                        [TrivRules]
% 1.73/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.73/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.00  --sup_immed_bw_main                     []
% 1.73/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.73/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/1.00  
% 1.73/1.00  ------ Combination Options
% 1.73/1.00  
% 1.73/1.00  --comb_res_mult                         3
% 1.73/1.00  --comb_sup_mult                         2
% 1.73/1.00  --comb_inst_mult                        10
% 1.73/1.00  
% 1.73/1.00  ------ Debug Options
% 1.73/1.00  
% 1.73/1.00  --dbg_backtrace                         false
% 1.73/1.00  --dbg_dump_prop_clauses                 false
% 1.73/1.00  --dbg_dump_prop_clauses_file            -
% 1.73/1.00  --dbg_out_stat                          false
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  ------ Proving...
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  % SZS status Theorem for theBenchmark.p
% 1.73/1.00  
% 1.73/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.73/1.00  
% 1.73/1.00  fof(f4,axiom,(
% 1.73/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f15,plain,(
% 1.73/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.73/1.00    inference(ennf_transformation,[],[f4])).
% 1.73/1.00  
% 1.73/1.00  fof(f22,plain,(
% 1.73/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.73/1.00    inference(nnf_transformation,[],[f15])).
% 1.73/1.00  
% 1.73/1.00  fof(f23,plain,(
% 1.73/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.73/1.00    inference(rectify,[],[f22])).
% 1.73/1.00  
% 1.73/1.00  fof(f24,plain,(
% 1.73/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK0(X0,X1,X2)),X2) & r2_hidden(sK0(X0,X1,X2),k2_relat_1(X2))))),
% 1.73/1.00    introduced(choice_axiom,[])).
% 1.73/1.00  
% 1.73/1.00  fof(f25,plain,(
% 1.73/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK0(X0,X1,X2)),X2) & r2_hidden(sK0(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 1.73/1.00  
% 1.73/1.00  fof(f37,plain,(
% 1.73/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK0(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f25])).
% 1.73/1.00  
% 1.73/1.00  fof(f9,conjecture,(
% 1.73/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 1.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f10,negated_conjecture,(
% 1.73/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 1.73/1.00    inference(negated_conjecture,[],[f9])).
% 1.73/1.00  
% 1.73/1.00  fof(f11,plain,(
% 1.73/1.00    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)))))),
% 1.73/1.00    inference(pure_predicate_removal,[],[f10])).
% 1.73/1.00  
% 1.73/1.00  fof(f21,plain,(
% 1.73/1.00    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.73/1.00    inference(ennf_transformation,[],[f11])).
% 1.73/1.00  
% 1.73/1.00  fof(f26,plain,(
% 1.73/1.00    ? [X0,X1,X2,X3] : (? [X4] : (((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.73/1.00    inference(nnf_transformation,[],[f21])).
% 1.73/1.00  
% 1.73/1.00  fof(f27,plain,(
% 1.73/1.00    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.73/1.00    inference(flattening,[],[f26])).
% 1.73/1.00  
% 1.73/1.00  fof(f28,plain,(
% 1.73/1.00    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.73/1.00    inference(rectify,[],[f27])).
% 1.73/1.00  
% 1.73/1.00  fof(f31,plain,(
% 1.73/1.00    ( ! [X4,X2,X3,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK6,X1) & r2_hidden(k4_tarski(X4,sK6),X3) & m1_subset_1(sK6,X2))) )),
% 1.73/1.00    introduced(choice_axiom,[])).
% 1.73/1.00  
% 1.73/1.00  fof(f30,plain,(
% 1.73/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) => ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(sK5,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(sK5,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(sK5,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(sK5,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(sK5,X0))) )),
% 1.73/1.00    introduced(choice_axiom,[])).
% 1.73/1.00  
% 1.73/1.00  fof(f29,plain,(
% 1.73/1.00    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (? [X4] : ((! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(k4_tarski(X4,X5),sK4) | ~m1_subset_1(X5,sK3)) | ~r2_hidden(X4,k8_relset_1(sK1,sK3,sK4,sK2))) & (? [X6] : (r2_hidden(X6,sK2) & r2_hidden(k4_tarski(X4,X6),sK4) & m1_subset_1(X6,sK3)) | r2_hidden(X4,k8_relset_1(sK1,sK3,sK4,sK2))) & m1_subset_1(X4,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))))),
% 1.73/1.00    introduced(choice_axiom,[])).
% 1.73/1.00  
% 1.73/1.00  fof(f32,plain,(
% 1.73/1.00    ((! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(k4_tarski(sK5,X5),sK4) | ~m1_subset_1(X5,sK3)) | ~r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2))) & ((r2_hidden(sK6,sK2) & r2_hidden(k4_tarski(sK5,sK6),sK4) & m1_subset_1(sK6,sK3)) | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2))) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 1.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f28,f31,f30,f29])).
% 1.73/1.00  
% 1.73/1.00  fof(f48,plain,(
% 1.73/1.00    r2_hidden(k4_tarski(sK5,sK6),sK4) | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2))),
% 1.73/1.00    inference(cnf_transformation,[],[f32])).
% 1.73/1.00  
% 1.73/1.00  fof(f50,plain,(
% 1.73/1.00    ( ! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(k4_tarski(sK5,X5),sK4) | ~m1_subset_1(X5,sK3) | ~r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2))) )),
% 1.73/1.00    inference(cnf_transformation,[],[f32])).
% 1.73/1.00  
% 1.73/1.00  fof(f45,plain,(
% 1.73/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 1.73/1.00    inference(cnf_transformation,[],[f32])).
% 1.73/1.00  
% 1.73/1.00  fof(f2,axiom,(
% 1.73/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f14,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.73/1.00    inference(ennf_transformation,[],[f2])).
% 1.73/1.00  
% 1.73/1.00  fof(f34,plain,(
% 1.73/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f14])).
% 1.73/1.00  
% 1.73/1.00  fof(f7,axiom,(
% 1.73/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f19,plain,(
% 1.73/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.73/1.00    inference(ennf_transformation,[],[f7])).
% 1.73/1.00  
% 1.73/1.00  fof(f43,plain,(
% 1.73/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.73/1.00    inference(cnf_transformation,[],[f19])).
% 1.73/1.00  
% 1.73/1.00  fof(f6,axiom,(
% 1.73/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f18,plain,(
% 1.73/1.00    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.73/1.00    inference(ennf_transformation,[],[f6])).
% 1.73/1.00  
% 1.73/1.00  fof(f42,plain,(
% 1.73/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.73/1.00    inference(cnf_transformation,[],[f18])).
% 1.73/1.00  
% 1.73/1.00  fof(f3,axiom,(
% 1.73/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f35,plain,(
% 1.73/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.73/1.00    inference(cnf_transformation,[],[f3])).
% 1.73/1.00  
% 1.73/1.00  fof(f8,axiom,(
% 1.73/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 1.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f20,plain,(
% 1.73/1.00    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.73/1.00    inference(ennf_transformation,[],[f8])).
% 1.73/1.00  
% 1.73/1.00  fof(f44,plain,(
% 1.73/1.00    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.73/1.00    inference(cnf_transformation,[],[f20])).
% 1.73/1.00  
% 1.73/1.00  fof(f36,plain,(
% 1.73/1.00    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f25])).
% 1.73/1.00  
% 1.73/1.00  fof(f38,plain,(
% 1.73/1.00    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f25])).
% 1.73/1.00  
% 1.73/1.00  fof(f1,axiom,(
% 1.73/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f12,plain,(
% 1.73/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.73/1.00    inference(ennf_transformation,[],[f1])).
% 1.73/1.00  
% 1.73/1.00  fof(f13,plain,(
% 1.73/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.73/1.00    inference(flattening,[],[f12])).
% 1.73/1.00  
% 1.73/1.00  fof(f33,plain,(
% 1.73/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f13])).
% 1.73/1.00  
% 1.73/1.00  fof(f39,plain,(
% 1.73/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f25])).
% 1.73/1.00  
% 1.73/1.00  fof(f5,axiom,(
% 1.73/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.73/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f16,plain,(
% 1.73/1.00    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 1.73/1.00    inference(ennf_transformation,[],[f5])).
% 1.73/1.00  
% 1.73/1.00  fof(f17,plain,(
% 1.73/1.00    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.73/1.00    inference(flattening,[],[f16])).
% 1.73/1.00  
% 1.73/1.00  fof(f41,plain,(
% 1.73/1.00    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f17])).
% 1.73/1.00  
% 1.73/1.00  fof(f49,plain,(
% 1.73/1.00    r2_hidden(sK6,sK2) | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2))),
% 1.73/1.00    inference(cnf_transformation,[],[f32])).
% 1.73/1.00  
% 1.73/1.00  fof(f47,plain,(
% 1.73/1.00    m1_subset_1(sK6,sK3) | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2))),
% 1.73/1.00    inference(cnf_transformation,[],[f32])).
% 1.73/1.00  
% 1.73/1.00  cnf(c_5,plain,
% 1.73/1.00      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 1.73/1.00      | r2_hidden(k4_tarski(X0,sK0(X0,X2,X1)),X1)
% 1.73/1.00      | ~ v1_relat_1(X1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_536,plain,
% 1.73/1.00      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 1.73/1.00      | r2_hidden(k4_tarski(X0,sK0(X0,X2,X1)),X1) = iProver_top
% 1.73/1.00      | v1_relat_1(X1) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_14,negated_conjecture,
% 1.73/1.00      ( r2_hidden(k4_tarski(sK5,sK6),sK4)
% 1.73/1.00      | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) ),
% 1.73/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_527,plain,
% 1.73/1.00      ( r2_hidden(k4_tarski(sK5,sK6),sK4) = iProver_top
% 1.73/1.00      | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_12,negated_conjecture,
% 1.73/1.00      ( ~ r2_hidden(X0,sK2)
% 1.73/1.00      | ~ r2_hidden(k4_tarski(sK5,X0),sK4)
% 1.73/1.00      | ~ r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2))
% 1.73/1.00      | ~ m1_subset_1(X0,sK3) ),
% 1.73/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_529,plain,
% 1.73/1.00      ( r2_hidden(X0,sK2) != iProver_top
% 1.73/1.00      | r2_hidden(k4_tarski(sK5,X0),sK4) != iProver_top
% 1.73/1.00      | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) != iProver_top
% 1.73/1.00      | m1_subset_1(X0,sK3) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_775,plain,
% 1.73/1.00      ( r2_hidden(X0,sK2) != iProver_top
% 1.73/1.00      | r2_hidden(k4_tarski(sK5,X0),sK4) != iProver_top
% 1.73/1.00      | r2_hidden(k4_tarski(sK5,sK6),sK4) = iProver_top
% 1.73/1.00      | m1_subset_1(X0,sK3) != iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_527,c_529]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1765,plain,
% 1.73/1.00      ( r2_hidden(sK0(sK5,X0,sK4),sK2) != iProver_top
% 1.73/1.00      | r2_hidden(k4_tarski(sK5,sK6),sK4) = iProver_top
% 1.73/1.00      | r2_hidden(sK5,k10_relat_1(sK4,X0)) != iProver_top
% 1.73/1.00      | m1_subset_1(sK0(sK5,X0,sK4),sK3) != iProver_top
% 1.73/1.00      | v1_relat_1(sK4) != iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_536,c_775]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_17,negated_conjecture,
% 1.73/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 1.73/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_18,plain,
% 1.73/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_21,plain,
% 1.73/1.00      ( r2_hidden(k4_tarski(sK5,sK6),sK4) = iProver_top
% 1.73/1.00      | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.73/1.00      | ~ v1_relat_1(X1)
% 1.73/1.00      | v1_relat_1(X0) ),
% 1.73/1.00      inference(cnf_transformation,[],[f34]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_673,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.73/1.00      | v1_relat_1(X0)
% 1.73/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_902,plain,
% 1.73/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 1.73/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK3))
% 1.73/1.00      | v1_relat_1(sK4) ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_673]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_903,plain,
% 1.73/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 1.73/1.00      | v1_relat_1(k2_zfmisc_1(sK1,sK3)) != iProver_top
% 1.73/1.00      | v1_relat_1(sK4) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_902]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_524,plain,
% 1.73/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_10,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.73/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.73/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_531,plain,
% 1.73/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.73/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_919,plain,
% 1.73/1.00      ( k2_relset_1(sK1,sK3,sK4) = k2_relat_1(sK4) ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_524,c_531]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_9,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.73/1.00      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 1.73/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_532,plain,
% 1.73/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.73/1.00      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1087,plain,
% 1.73/1.00      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top
% 1.73/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_919,c_532]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2,plain,
% 1.73/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.73/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1138,plain,
% 1.73/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK3)) ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1139,plain,
% 1.73/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK3)) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_1138]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_11,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.73/1.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 1.73/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_530,plain,
% 1.73/1.00      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 1.73/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_897,plain,
% 1.73/1.00      ( k8_relset_1(sK1,sK3,sK4,X0) = k10_relat_1(sK4,X0) ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_524,c_530]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1149,plain,
% 1.73/1.00      ( r2_hidden(k4_tarski(sK5,sK6),sK4) = iProver_top
% 1.73/1.00      | r2_hidden(sK5,k10_relat_1(sK4,sK2)) = iProver_top ),
% 1.73/1.00      inference(demodulation,[status(thm)],[c_897,c_527]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_6,plain,
% 1.73/1.00      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 1.73/1.00      | r2_hidden(sK0(X0,X2,X1),k2_relat_1(X1))
% 1.73/1.00      | ~ v1_relat_1(X1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f36]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_932,plain,
% 1.73/1.00      ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
% 1.73/1.00      | r2_hidden(sK0(X0,X1,sK4),k2_relat_1(sK4))
% 1.73/1.00      | ~ v1_relat_1(sK4) ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1716,plain,
% 1.73/1.00      ( r2_hidden(sK0(sK5,sK2,sK4),k2_relat_1(sK4))
% 1.73/1.00      | ~ r2_hidden(sK5,k10_relat_1(sK4,sK2))
% 1.73/1.00      | ~ v1_relat_1(sK4) ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_932]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1717,plain,
% 1.73/1.00      ( r2_hidden(sK0(sK5,sK2,sK4),k2_relat_1(sK4)) = iProver_top
% 1.73/1.00      | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
% 1.73/1.00      | v1_relat_1(sK4) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_1716]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_931,plain,
% 1.73/1.00      ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
% 1.73/1.00      | r2_hidden(k4_tarski(X0,sK0(X0,X1,sK4)),sK4)
% 1.73/1.00      | ~ v1_relat_1(sK4) ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1715,plain,
% 1.73/1.00      ( r2_hidden(k4_tarski(sK5,sK0(sK5,sK2,sK4)),sK4)
% 1.73/1.00      | ~ r2_hidden(sK5,k10_relat_1(sK4,sK2))
% 1.73/1.00      | ~ v1_relat_1(sK4) ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_931]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1719,plain,
% 1.73/1.00      ( r2_hidden(k4_tarski(sK5,sK0(sK5,sK2,sK4)),sK4) = iProver_top
% 1.73/1.00      | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
% 1.73/1.00      | v1_relat_1(sK4) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_1715]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_4,plain,
% 1.73/1.00      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 1.73/1.00      | r2_hidden(sK0(X0,X2,X1),X2)
% 1.73/1.00      | ~ v1_relat_1(X1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_933,plain,
% 1.73/1.00      ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
% 1.73/1.00      | r2_hidden(sK0(X0,X1,sK4),X1)
% 1.73/1.00      | ~ v1_relat_1(sK4) ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1714,plain,
% 1.73/1.00      ( r2_hidden(sK0(sK5,sK2,sK4),sK2)
% 1.73/1.00      | ~ r2_hidden(sK5,k10_relat_1(sK4,sK2))
% 1.73/1.00      | ~ v1_relat_1(sK4) ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_933]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1721,plain,
% 1.73/1.00      ( r2_hidden(sK0(sK5,sK2,sK4),sK2) = iProver_top
% 1.73/1.00      | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
% 1.73/1.00      | v1_relat_1(sK4) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_1714]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2091,plain,
% 1.73/1.00      ( ~ r2_hidden(sK0(sK5,sK2,sK4),sK2)
% 1.73/1.00      | ~ r2_hidden(k4_tarski(sK5,sK0(sK5,sK2,sK4)),sK4)
% 1.73/1.00      | ~ r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2))
% 1.73/1.00      | ~ m1_subset_1(sK0(sK5,sK2,sK4),sK3) ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2092,plain,
% 1.73/1.00      ( r2_hidden(sK0(sK5,sK2,sK4),sK2) != iProver_top
% 1.73/1.00      | r2_hidden(k4_tarski(sK5,sK0(sK5,sK2,sK4)),sK4) != iProver_top
% 1.73/1.00      | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) != iProver_top
% 1.73/1.00      | m1_subset_1(sK0(sK5,sK2,sK4),sK3) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_2091]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_0,plain,
% 1.73/1.00      ( ~ r2_hidden(X0,X1)
% 1.73/1.00      | m1_subset_1(X0,X2)
% 1.73/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 1.73/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2138,plain,
% 1.73/1.00      ( ~ r2_hidden(sK0(sK5,sK2,sK4),k2_relat_1(sK4))
% 1.73/1.00      | m1_subset_1(sK0(sK5,sK2,sK4),X0)
% 1.73/1.00      | ~ m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2139,plain,
% 1.73/1.00      ( r2_hidden(sK0(sK5,sK2,sK4),k2_relat_1(sK4)) != iProver_top
% 1.73/1.00      | m1_subset_1(sK0(sK5,sK2,sK4),X0) = iProver_top
% 1.73/1.00      | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(X0)) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_2138]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2141,plain,
% 1.73/1.00      ( r2_hidden(sK0(sK5,sK2,sK4),k2_relat_1(sK4)) != iProver_top
% 1.73/1.00      | m1_subset_1(sK0(sK5,sK2,sK4),sK3) = iProver_top
% 1.73/1.00      | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) != iProver_top ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_2139]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2240,plain,
% 1.73/1.00      ( r2_hidden(k4_tarski(sK5,sK6),sK4) = iProver_top ),
% 1.73/1.00      inference(global_propositional_subsumption,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_1765,c_18,c_21,c_903,c_1087,c_1139,c_1149,c_1717,
% 1.73/1.00                 c_1719,c_1721,c_2092,c_2141]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_3,plain,
% 1.73/1.00      ( ~ r2_hidden(X0,X1)
% 1.73/1.00      | r2_hidden(X2,k10_relat_1(X3,X1))
% 1.73/1.00      | ~ r2_hidden(X0,k2_relat_1(X3))
% 1.73/1.00      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 1.73/1.00      | ~ v1_relat_1(X3) ),
% 1.73/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_538,plain,
% 1.73/1.00      ( r2_hidden(X0,X1) != iProver_top
% 1.73/1.00      | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
% 1.73/1.00      | r2_hidden(X0,k2_relat_1(X3)) != iProver_top
% 1.73/1.00      | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
% 1.73/1.00      | v1_relat_1(X3) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_7,plain,
% 1.73/1.00      ( r2_hidden(X0,k2_relat_1(X1))
% 1.73/1.00      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 1.73/1.00      | ~ v1_relat_1(X1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_534,plain,
% 1.73/1.00      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 1.73/1.00      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 1.73/1.00      | v1_relat_1(X1) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_627,plain,
% 1.73/1.00      ( r2_hidden(X0,X1) != iProver_top
% 1.73/1.00      | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
% 1.73/1.00      | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
% 1.73/1.00      | v1_relat_1(X3) != iProver_top ),
% 1.73/1.00      inference(forward_subsumption_resolution,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_538,c_534]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2440,plain,
% 1.73/1.00      ( r2_hidden(sK6,X0) != iProver_top
% 1.73/1.00      | r2_hidden(sK5,k10_relat_1(sK4,X0)) = iProver_top
% 1.73/1.00      | v1_relat_1(sK4) != iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_2240,c_627]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2537,plain,
% 1.73/1.00      ( r2_hidden(sK5,k10_relat_1(sK4,X0)) = iProver_top
% 1.73/1.00      | r2_hidden(sK6,X0) != iProver_top ),
% 1.73/1.00      inference(global_propositional_subsumption,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_2440,c_18,c_903,c_1139]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2538,plain,
% 1.73/1.00      ( r2_hidden(sK6,X0) != iProver_top
% 1.73/1.00      | r2_hidden(sK5,k10_relat_1(sK4,X0)) = iProver_top ),
% 1.73/1.00      inference(renaming,[status(thm)],[c_2537]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1152,plain,
% 1.73/1.00      ( r2_hidden(X0,sK2) != iProver_top
% 1.73/1.00      | r2_hidden(k4_tarski(sK5,X0),sK4) != iProver_top
% 1.73/1.00      | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
% 1.73/1.00      | m1_subset_1(X0,sK3) != iProver_top ),
% 1.73/1.00      inference(demodulation,[status(thm)],[c_897,c_529]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2247,plain,
% 1.73/1.00      ( r2_hidden(sK6,sK2) != iProver_top
% 1.73/1.00      | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
% 1.73/1.00      | m1_subset_1(sK6,sK3) != iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_2240,c_1152]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_537,plain,
% 1.73/1.00      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 1.73/1.00      | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
% 1.73/1.00      | v1_relat_1(X1) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_13,negated_conjecture,
% 1.73/1.00      ( r2_hidden(sK6,sK2)
% 1.73/1.00      | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) ),
% 1.73/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_528,plain,
% 1.73/1.00      ( r2_hidden(sK6,sK2) = iProver_top
% 1.73/1.00      | r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_768,plain,
% 1.73/1.00      ( r2_hidden(X0,sK2) != iProver_top
% 1.73/1.00      | r2_hidden(k4_tarski(sK5,X0),sK4) != iProver_top
% 1.73/1.00      | r2_hidden(sK6,sK2) = iProver_top
% 1.73/1.00      | m1_subset_1(X0,sK3) != iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_528,c_529]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1766,plain,
% 1.73/1.00      ( r2_hidden(sK0(sK5,X0,sK4),sK2) != iProver_top
% 1.73/1.00      | r2_hidden(sK6,sK2) = iProver_top
% 1.73/1.00      | r2_hidden(sK5,k10_relat_1(sK4,X0)) != iProver_top
% 1.73/1.00      | m1_subset_1(sK0(sK5,X0,sK4),sK3) != iProver_top
% 1.73/1.00      | v1_relat_1(sK4) != iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_536,c_768]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2099,plain,
% 1.73/1.00      ( m1_subset_1(sK0(sK5,X0,sK4),sK3) != iProver_top
% 1.73/1.00      | r2_hidden(sK5,k10_relat_1(sK4,X0)) != iProver_top
% 1.73/1.00      | r2_hidden(sK6,sK2) = iProver_top
% 1.73/1.00      | r2_hidden(sK0(sK5,X0,sK4),sK2) != iProver_top ),
% 1.73/1.00      inference(global_propositional_subsumption,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_1766,c_18,c_903,c_1139]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2100,plain,
% 1.73/1.00      ( r2_hidden(sK0(sK5,X0,sK4),sK2) != iProver_top
% 1.73/1.00      | r2_hidden(sK6,sK2) = iProver_top
% 1.73/1.00      | r2_hidden(sK5,k10_relat_1(sK4,X0)) != iProver_top
% 1.73/1.00      | m1_subset_1(sK0(sK5,X0,sK4),sK3) != iProver_top ),
% 1.73/1.00      inference(renaming,[status(thm)],[c_2099]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_535,plain,
% 1.73/1.00      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 1.73/1.00      | r2_hidden(sK0(X0,X2,X1),k2_relat_1(X1)) = iProver_top
% 1.73/1.00      | v1_relat_1(X1) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1463,plain,
% 1.73/1.00      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
% 1.73/1.00      inference(global_propositional_subsumption,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_1087,c_18]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_541,plain,
% 1.73/1.00      ( r2_hidden(X0,X1) != iProver_top
% 1.73/1.00      | m1_subset_1(X0,X2) = iProver_top
% 1.73/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1468,plain,
% 1.73/1.00      ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
% 1.73/1.00      | m1_subset_1(X0,sK3) = iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_1463,c_541]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1592,plain,
% 1.73/1.00      ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
% 1.73/1.00      | m1_subset_1(sK0(X0,X1,sK4),sK3) = iProver_top
% 1.73/1.00      | v1_relat_1(sK4) != iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_535,c_1468]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1669,plain,
% 1.73/1.00      ( m1_subset_1(sK0(X0,X1,sK4),sK3) = iProver_top
% 1.73/1.00      | r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top ),
% 1.73/1.00      inference(global_propositional_subsumption,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_1592,c_18,c_903,c_1139]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1670,plain,
% 1.73/1.00      ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
% 1.73/1.00      | m1_subset_1(sK0(X0,X1,sK4),sK3) = iProver_top ),
% 1.73/1.00      inference(renaming,[status(thm)],[c_1669]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2109,plain,
% 1.73/1.00      ( r2_hidden(sK0(sK5,X0,sK4),sK2) != iProver_top
% 1.73/1.00      | r2_hidden(sK6,sK2) = iProver_top
% 1.73/1.00      | r2_hidden(sK5,k10_relat_1(sK4,X0)) != iProver_top ),
% 1.73/1.00      inference(forward_subsumption_resolution,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_2100,c_1670]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2113,plain,
% 1.73/1.00      ( r2_hidden(sK6,sK2) = iProver_top
% 1.73/1.00      | r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top
% 1.73/1.00      | v1_relat_1(sK4) != iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_537,c_2109]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_15,negated_conjecture,
% 1.73/1.00      ( r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2))
% 1.73/1.00      | m1_subset_1(sK6,sK3) ),
% 1.73/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_526,plain,
% 1.73/1.00      ( r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) = iProver_top
% 1.73/1.00      | m1_subset_1(sK6,sK3) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_736,plain,
% 1.73/1.00      ( r2_hidden(X0,sK2) != iProver_top
% 1.73/1.00      | r2_hidden(k4_tarski(sK5,X0),sK4) != iProver_top
% 1.73/1.00      | m1_subset_1(X0,sK3) != iProver_top
% 1.73/1.00      | m1_subset_1(sK6,sK3) = iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_526,c_529]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1767,plain,
% 1.73/1.00      ( r2_hidden(sK0(sK5,X0,sK4),sK2) != iProver_top
% 1.73/1.00      | r2_hidden(sK5,k10_relat_1(sK4,X0)) != iProver_top
% 1.73/1.00      | m1_subset_1(sK0(sK5,X0,sK4),sK3) != iProver_top
% 1.73/1.00      | m1_subset_1(sK6,sK3) = iProver_top
% 1.73/1.00      | v1_relat_1(sK4) != iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_536,c_736]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_20,plain,
% 1.73/1.00      ( r2_hidden(sK5,k8_relset_1(sK1,sK3,sK4,sK2)) = iProver_top
% 1.73/1.00      | m1_subset_1(sK6,sK3) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1151,plain,
% 1.73/1.00      ( r2_hidden(sK5,k10_relat_1(sK4,sK2)) = iProver_top
% 1.73/1.00      | m1_subset_1(sK6,sK3) = iProver_top ),
% 1.73/1.00      inference(demodulation,[status(thm)],[c_897,c_526]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2234,plain,
% 1.73/1.00      ( m1_subset_1(sK6,sK3) = iProver_top ),
% 1.73/1.00      inference(global_propositional_subsumption,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_1767,c_18,c_20,c_903,c_1087,c_1139,c_1151,c_1717,
% 1.73/1.00                 c_1719,c_1721,c_2092,c_2141]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2299,plain,
% 1.73/1.00      ( r2_hidden(sK5,k10_relat_1(sK4,sK2)) != iProver_top ),
% 1.73/1.00      inference(global_propositional_subsumption,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_2247,c_18,c_20,c_903,c_1087,c_1139,c_1151,c_1717,
% 1.73/1.00                 c_1719,c_1721,c_2092,c_2113,c_2141]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2546,plain,
% 1.73/1.00      ( r2_hidden(sK6,sK2) != iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_2538,c_2299]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1150,plain,
% 1.73/1.00      ( r2_hidden(sK6,sK2) = iProver_top
% 1.73/1.00      | r2_hidden(sK5,k10_relat_1(sK4,sK2)) = iProver_top ),
% 1.73/1.00      inference(demodulation,[status(thm)],[c_897,c_528]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(contradiction,plain,
% 1.73/1.00      ( $false ),
% 1.73/1.00      inference(minisat,[status(thm)],[c_2546,c_2299,c_1150]) ).
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.73/1.00  
% 1.73/1.00  ------                               Statistics
% 1.73/1.00  
% 1.73/1.00  ------ General
% 1.73/1.00  
% 1.73/1.00  abstr_ref_over_cycles:                  0
% 1.73/1.00  abstr_ref_under_cycles:                 0
% 1.73/1.00  gc_basic_clause_elim:                   0
% 1.73/1.00  forced_gc_time:                         0
% 1.73/1.00  parsing_time:                           0.009
% 1.73/1.00  unif_index_cands_time:                  0.
% 1.73/1.00  unif_index_add_time:                    0.
% 1.73/1.00  orderings_time:                         0.
% 1.73/1.00  out_proof_time:                         0.012
% 1.73/1.00  total_time:                             0.124
% 1.73/1.00  num_of_symbols:                         49
% 1.73/1.00  num_of_terms:                           2078
% 1.73/1.00  
% 1.73/1.00  ------ Preprocessing
% 1.73/1.00  
% 1.73/1.00  num_of_splits:                          0
% 1.73/1.00  num_of_split_atoms:                     0
% 1.73/1.00  num_of_reused_defs:                     0
% 1.73/1.00  num_eq_ax_congr_red:                    20
% 1.73/1.00  num_of_sem_filtered_clauses:            1
% 1.73/1.00  num_of_subtypes:                        1
% 1.73/1.00  monotx_restored_types:                  0
% 1.73/1.00  sat_num_of_epr_types:                   0
% 1.73/1.00  sat_num_of_non_cyclic_types:            0
% 1.73/1.00  sat_guarded_non_collapsed_types:        0
% 1.73/1.00  num_pure_diseq_elim:                    0
% 1.73/1.00  simp_replaced_by:                       0
% 1.73/1.00  res_preprocessed:                       73
% 1.73/1.00  prep_upred:                             0
% 1.73/1.00  prep_unflattend:                        0
% 1.73/1.00  smt_new_axioms:                         0
% 1.73/1.00  pred_elim_cands:                        3
% 1.73/1.00  pred_elim:                              0
% 1.73/1.00  pred_elim_cl:                           0
% 1.73/1.00  pred_elim_cycles:                       1
% 1.73/1.00  merged_defs:                            0
% 1.73/1.00  merged_defs_ncl:                        0
% 1.73/1.00  bin_hyper_res:                          0
% 1.73/1.00  prep_cycles:                            3
% 1.73/1.00  pred_elim_time:                         0.
% 1.73/1.00  splitting_time:                         0.
% 1.73/1.00  sem_filter_time:                        0.
% 1.73/1.00  monotx_time:                            0.
% 1.73/1.00  subtype_inf_time:                       0.
% 1.73/1.00  
% 1.73/1.00  ------ Problem properties
% 1.73/1.00  
% 1.73/1.00  clauses:                                18
% 1.73/1.00  conjectures:                            6
% 1.73/1.00  epr:                                    1
% 1.73/1.00  horn:                                   15
% 1.73/1.00  ground:                                 5
% 1.73/1.00  unary:                                  3
% 1.73/1.00  binary:                                 6
% 1.73/1.00  lits:                                   45
% 1.73/1.00  lits_eq:                                2
% 1.73/1.00  fd_pure:                                0
% 1.73/1.00  fd_pseudo:                              0
% 1.73/1.00  fd_cond:                                0
% 1.73/1.00  fd_pseudo_cond:                         0
% 1.73/1.00  ac_symbols:                             0
% 1.73/1.00  
% 1.73/1.00  ------ Propositional Solver
% 1.73/1.00  
% 1.73/1.00  prop_solver_calls:                      26
% 1.73/1.00  prop_fast_solver_calls:                 541
% 1.73/1.00  smt_solver_calls:                       0
% 1.73/1.00  smt_fast_solver_calls:                  0
% 1.73/1.00  prop_num_of_clauses:                    820
% 1.73/1.00  prop_preprocess_simplified:             3022
% 1.73/1.00  prop_fo_subsumed:                       21
% 1.73/1.00  prop_solver_time:                       0.
% 1.73/1.00  smt_solver_time:                        0.
% 1.73/1.00  smt_fast_solver_time:                   0.
% 1.73/1.00  prop_fast_solver_time:                  0.
% 1.73/1.00  prop_unsat_core_time:                   0.
% 1.73/1.00  
% 1.73/1.00  ------ QBF
% 1.73/1.00  
% 1.73/1.00  qbf_q_res:                              0
% 1.73/1.00  qbf_num_tautologies:                    0
% 1.73/1.00  qbf_prep_cycles:                        0
% 1.73/1.00  
% 1.73/1.00  ------ BMC1
% 1.73/1.00  
% 1.73/1.00  bmc1_current_bound:                     -1
% 1.73/1.00  bmc1_last_solved_bound:                 -1
% 1.73/1.00  bmc1_unsat_core_size:                   -1
% 1.73/1.00  bmc1_unsat_core_parents_size:           -1
% 1.73/1.00  bmc1_merge_next_fun:                    0
% 1.73/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.73/1.00  
% 1.73/1.00  ------ Instantiation
% 1.73/1.00  
% 1.73/1.00  inst_num_of_clauses:                    278
% 1.73/1.00  inst_num_in_passive:                    10
% 1.73/1.00  inst_num_in_active:                     224
% 1.73/1.00  inst_num_in_unprocessed:                44
% 1.73/1.00  inst_num_of_loops:                      250
% 1.73/1.00  inst_num_of_learning_restarts:          0
% 1.73/1.00  inst_num_moves_active_passive:          21
% 1.73/1.00  inst_lit_activity:                      0
% 1.73/1.00  inst_lit_activity_moves:                0
% 1.73/1.00  inst_num_tautologies:                   0
% 1.73/1.00  inst_num_prop_implied:                  0
% 1.73/1.00  inst_num_existing_simplified:           0
% 1.73/1.00  inst_num_eq_res_simplified:             0
% 1.73/1.00  inst_num_child_elim:                    0
% 1.73/1.00  inst_num_of_dismatching_blockings:      98
% 1.73/1.00  inst_num_of_non_proper_insts:           333
% 1.73/1.00  inst_num_of_duplicates:                 0
% 1.73/1.00  inst_inst_num_from_inst_to_res:         0
% 1.73/1.00  inst_dismatching_checking_time:         0.
% 1.73/1.00  
% 1.73/1.00  ------ Resolution
% 1.73/1.00  
% 1.73/1.00  res_num_of_clauses:                     0
% 1.73/1.00  res_num_in_passive:                     0
% 1.73/1.00  res_num_in_active:                      0
% 1.73/1.00  res_num_of_loops:                       76
% 1.73/1.00  res_forward_subset_subsumed:            66
% 1.73/1.00  res_backward_subset_subsumed:           2
% 1.73/1.00  res_forward_subsumed:                   0
% 1.73/1.00  res_backward_subsumed:                  0
% 1.73/1.00  res_forward_subsumption_resolution:     0
% 1.73/1.00  res_backward_subsumption_resolution:    0
% 1.73/1.00  res_clause_to_clause_subsumption:       91
% 1.73/1.00  res_orphan_elimination:                 0
% 1.73/1.00  res_tautology_del:                      68
% 1.73/1.00  res_num_eq_res_simplified:              0
% 1.73/1.00  res_num_sel_changes:                    0
% 1.73/1.00  res_moves_from_active_to_pass:          0
% 1.73/1.00  
% 1.73/1.00  ------ Superposition
% 1.73/1.00  
% 1.73/1.00  sup_time_total:                         0.
% 1.73/1.00  sup_time_generating:                    0.
% 1.73/1.00  sup_time_sim_full:                      0.
% 1.73/1.00  sup_time_sim_immed:                     0.
% 1.73/1.00  
% 1.73/1.00  sup_num_of_clauses:                     51
% 1.73/1.00  sup_num_in_active:                      43
% 1.73/1.00  sup_num_in_passive:                     8
% 1.73/1.00  sup_num_of_loops:                       49
% 1.73/1.00  sup_fw_superposition:                   28
% 1.73/1.00  sup_bw_superposition:                   29
% 1.73/1.00  sup_immediate_simplified:               7
% 1.73/1.00  sup_given_eliminated:                   0
% 1.73/1.00  comparisons_done:                       0
% 1.73/1.00  comparisons_avoided:                    0
% 1.73/1.00  
% 1.73/1.00  ------ Simplifications
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  sim_fw_subset_subsumed:                 4
% 1.73/1.00  sim_bw_subset_subsumed:                 6
% 1.73/1.00  sim_fw_subsumed:                        1
% 1.73/1.00  sim_bw_subsumed:                        2
% 1.73/1.00  sim_fw_subsumption_res:                 2
% 1.73/1.00  sim_bw_subsumption_res:                 0
% 1.73/1.00  sim_tautology_del:                      5
% 1.73/1.00  sim_eq_tautology_del:                   0
% 1.73/1.00  sim_eq_res_simp:                        0
% 1.73/1.00  sim_fw_demodulated:                     0
% 1.73/1.00  sim_bw_demodulated:                     4
% 1.73/1.00  sim_light_normalised:                   1
% 1.73/1.00  sim_joinable_taut:                      0
% 1.73/1.00  sim_joinable_simp:                      0
% 1.73/1.00  sim_ac_normalised:                      0
% 1.73/1.00  sim_smt_subsumption:                    0
% 1.73/1.00  
%------------------------------------------------------------------------------

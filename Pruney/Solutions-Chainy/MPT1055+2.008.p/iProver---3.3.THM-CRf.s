%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:09 EST 2020

% Result     : Theorem 7.24s
% Output     : CNFRefutation 7.24s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 914 expanded)
%              Number of clauses        :   89 ( 246 expanded)
%              Number of leaves         :   23 ( 286 expanded)
%              Depth                    :   23
%              Number of atoms          :  496 (7094 expanded)
%              Number of equality atoms :  144 ( 344 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f3,f36])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(X1))
                     => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(X1))
                       => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                        <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
            | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
          & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
            | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
     => ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,sK5))
          | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),sK5) )
        & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,sK5))
          | r1_tarski(k7_relset_1(X0,X1,X2,X3),sK5) )
        & m1_subset_1(sK5,k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
              & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
              & m1_subset_1(X4,k1_zfmisc_1(X1)) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ? [X4] :
            ( ( ~ r1_tarski(sK4,k8_relset_1(X0,X1,X2,X4))
              | ~ r1_tarski(k7_relset_1(X0,X1,X2,sK4),X4) )
            & ( r1_tarski(sK4,k8_relset_1(X0,X1,X2,X4))
              | r1_tarski(k7_relset_1(X0,X1,X2,sK4),X4) )
            & m1_subset_1(X4,k1_zfmisc_1(X1)) )
        & m1_subset_1(sK4,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                    | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                  & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                    | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                  & m1_subset_1(X4,k1_zfmisc_1(X1)) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,sK3,X4))
                  | ~ r1_tarski(k7_relset_1(X0,X1,sK3,X3),X4) )
                & ( r1_tarski(X3,k8_relset_1(X0,X1,sK3,X4))
                  | r1_tarski(k7_relset_1(X0,X1,sK3,X3),X4) )
                & m1_subset_1(X4,k1_zfmisc_1(X1)) )
            & m1_subset_1(X3,k1_zfmisc_1(X0)) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK3,X0,X1)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ r1_tarski(X3,k8_relset_1(X0,sK2,X2,X4))
                      | ~ r1_tarski(k7_relset_1(X0,sK2,X2,X3),X4) )
                    & ( r1_tarski(X3,k8_relset_1(X0,sK2,X2,X4))
                      | r1_tarski(k7_relset_1(X0,sK2,X2,X3),X4) )
                    & m1_subset_1(X4,k1_zfmisc_1(sK2)) )
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
            & v1_funct_2(X2,X0,sK2)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                          | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                        & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                          | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                        & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                    & m1_subset_1(X3,k1_zfmisc_1(X0)) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(sK1,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(sK1,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(sK1,X1,X2,X4))
                        | r1_tarski(k7_relset_1(sK1,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(sK1)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
              & v1_funct_2(X2,sK1,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5))
      | ~ r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) )
    & ( r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5))
      | r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) )
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f40,f45,f44,f43,f42,f41])).

fof(f66,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,
    ( r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5))
    | r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,
    ( ~ r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5))
    | ~ r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_2,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2161,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_399,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_400,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | k8_relset_1(sK1,sK2,sK3,sK2) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_402,plain,
    ( k8_relset_1(sK1,sK2,sK3,sK2) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_400,c_22,c_20])).

cnf(c_2149,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2154,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3195,plain,
    ( k8_relset_1(sK1,sK2,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2149,c_2154])).

cnf(c_3786,plain,
    ( k10_relat_1(sK3,sK2) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_402,c_3195])).

cnf(c_7,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2157,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4021,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3786,c_2157])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2334,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2335,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2334])).

cnf(c_5885,plain,
    ( r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4021,c_29,c_2335])).

cnf(c_5886,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5885])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2163,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5891,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(X0,k1_relat_1(sK3)) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5886,c_2163])).

cnf(c_7550,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_relat_1(sK3)) = iProver_top
    | r1_tarski(X1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5891,c_2163])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_189,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_190,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_189])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_634,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_190,c_19])).

cnf(c_635,plain,
    ( r1_tarski(sK4,X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_636,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_638,plain,
    ( k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
    | r1_tarski(sK4,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_636])).

cnf(c_1642,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1652,plain,
    ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1642])).

cnf(c_1638,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1661,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1638])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)
    | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2152,plain,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) = iProver_top
    | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3774,plain,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) = iProver_top
    | r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3195,c_2152])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2155,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3482,plain,
    ( k7_relset_1(sK1,sK2,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2149,c_2155])).

cnf(c_4179,plain,
    ( r1_tarski(k9_relat_1(sK3,sK4),sK5) = iProver_top
    | r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3774,c_3482])).

cnf(c_9,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_428,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_429,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,X1))
    | ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ r1_tarski(k9_relat_1(sK3,X0),X1)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_2144,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_430,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_2550,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2144,c_29,c_430,c_2335])).

cnf(c_2551,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2550])).

cnf(c_4184,plain,
    ( r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4179,c_2551])).

cnf(c_5021,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,sK5)) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4184,c_2163])).

cnf(c_12355,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,k10_relat_1(sK3,sK5))) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X0),sK4) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5021,c_2551])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)
    | ~ r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2153,plain,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) != iProver_top
    | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3775,plain,
    ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) != iProver_top
    | r1_tarski(sK4,k10_relat_1(sK3,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3195,c_2153])).

cnf(c_4015,plain,
    ( r1_tarski(k9_relat_1(sK3,sK4),sK5) != iProver_top
    | r1_tarski(sK4,k10_relat_1(sK3,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3775,c_3482])).

cnf(c_5022,plain,
    ( r1_tarski(k9_relat_1(sK3,sK4),sK5) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4184,c_4015])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2158,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_416,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_417,plain,
    ( r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,X0)),X0)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_2145,plain,
    ( r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,X0)),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_418,plain,
    ( r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,X0)),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_3014,plain,
    ( r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,X0)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2145,c_29,c_418,c_2335])).

cnf(c_3538,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k9_relat_1(sK3,k10_relat_1(sK3,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3014,c_2163])).

cnf(c_5215,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,X1)) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X0),X1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2158,c_3538])).

cnf(c_12431,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),X1) = iProver_top
    | r1_tarski(X0,k10_relat_1(sK3,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5215,c_29,c_2335])).

cnf(c_12432,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,X1)) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X0),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_12431])).

cnf(c_12445,plain,
    ( r1_tarski(k9_relat_1(sK3,sK4),sK5) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4184,c_12432])).

cnf(c_13112,plain,
    ( r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12355,c_5022,c_12445])).

cnf(c_13117,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK4,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5891,c_13112])).

cnf(c_22376,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7550,c_638,c_1652,c_1661,c_13117])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ r1_tarski(X1,X0)
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_3,c_10])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ r1_tarski(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_334,c_23])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r1_tarski(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_2148,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_22433,plain,
    ( m1_subset_1(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22376,c_2148])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_76,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_25207,plain,
    ( m1_subset_1(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22433,c_76])).

cnf(c_25214,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2161,c_25207])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:01:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.24/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.24/1.48  
% 7.24/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.24/1.48  
% 7.24/1.48  ------  iProver source info
% 7.24/1.48  
% 7.24/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.24/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.24/1.48  git: non_committed_changes: false
% 7.24/1.48  git: last_make_outside_of_git: false
% 7.24/1.48  
% 7.24/1.48  ------ 
% 7.24/1.48  
% 7.24/1.48  ------ Input Options
% 7.24/1.48  
% 7.24/1.48  --out_options                           all
% 7.24/1.48  --tptp_safe_out                         true
% 7.24/1.48  --problem_path                          ""
% 7.24/1.48  --include_path                          ""
% 7.24/1.48  --clausifier                            res/vclausify_rel
% 7.24/1.48  --clausifier_options                    --mode clausify
% 7.24/1.48  --stdin                                 false
% 7.24/1.48  --stats_out                             all
% 7.24/1.48  
% 7.24/1.48  ------ General Options
% 7.24/1.48  
% 7.24/1.48  --fof                                   false
% 7.24/1.48  --time_out_real                         305.
% 7.24/1.48  --time_out_virtual                      -1.
% 7.24/1.48  --symbol_type_check                     false
% 7.24/1.48  --clausify_out                          false
% 7.24/1.48  --sig_cnt_out                           false
% 7.24/1.48  --trig_cnt_out                          false
% 7.24/1.48  --trig_cnt_out_tolerance                1.
% 7.24/1.48  --trig_cnt_out_sk_spl                   false
% 7.24/1.48  --abstr_cl_out                          false
% 7.24/1.48  
% 7.24/1.48  ------ Global Options
% 7.24/1.48  
% 7.24/1.48  --schedule                              default
% 7.24/1.48  --add_important_lit                     false
% 7.24/1.48  --prop_solver_per_cl                    1000
% 7.24/1.48  --min_unsat_core                        false
% 7.24/1.48  --soft_assumptions                      false
% 7.24/1.48  --soft_lemma_size                       3
% 7.24/1.48  --prop_impl_unit_size                   0
% 7.24/1.48  --prop_impl_unit                        []
% 7.24/1.48  --share_sel_clauses                     true
% 7.24/1.48  --reset_solvers                         false
% 7.24/1.48  --bc_imp_inh                            [conj_cone]
% 7.24/1.48  --conj_cone_tolerance                   3.
% 7.24/1.48  --extra_neg_conj                        none
% 7.24/1.48  --large_theory_mode                     true
% 7.24/1.48  --prolific_symb_bound                   200
% 7.24/1.48  --lt_threshold                          2000
% 7.24/1.48  --clause_weak_htbl                      true
% 7.24/1.48  --gc_record_bc_elim                     false
% 7.24/1.48  
% 7.24/1.48  ------ Preprocessing Options
% 7.24/1.48  
% 7.24/1.48  --preprocessing_flag                    true
% 7.24/1.48  --time_out_prep_mult                    0.1
% 7.24/1.48  --splitting_mode                        input
% 7.24/1.48  --splitting_grd                         true
% 7.24/1.48  --splitting_cvd                         false
% 7.24/1.48  --splitting_cvd_svl                     false
% 7.24/1.48  --splitting_nvd                         32
% 7.24/1.48  --sub_typing                            true
% 7.24/1.48  --prep_gs_sim                           true
% 7.24/1.48  --prep_unflatten                        true
% 7.24/1.48  --prep_res_sim                          true
% 7.24/1.48  --prep_upred                            true
% 7.24/1.48  --prep_sem_filter                       exhaustive
% 7.24/1.48  --prep_sem_filter_out                   false
% 7.24/1.48  --pred_elim                             true
% 7.24/1.48  --res_sim_input                         true
% 7.24/1.48  --eq_ax_congr_red                       true
% 7.24/1.48  --pure_diseq_elim                       true
% 7.24/1.48  --brand_transform                       false
% 7.24/1.48  --non_eq_to_eq                          false
% 7.24/1.48  --prep_def_merge                        true
% 7.24/1.48  --prep_def_merge_prop_impl              false
% 7.24/1.48  --prep_def_merge_mbd                    true
% 7.24/1.48  --prep_def_merge_tr_red                 false
% 7.24/1.48  --prep_def_merge_tr_cl                  false
% 7.24/1.48  --smt_preprocessing                     true
% 7.24/1.48  --smt_ac_axioms                         fast
% 7.24/1.48  --preprocessed_out                      false
% 7.24/1.48  --preprocessed_stats                    false
% 7.24/1.48  
% 7.24/1.48  ------ Abstraction refinement Options
% 7.24/1.48  
% 7.24/1.48  --abstr_ref                             []
% 7.24/1.48  --abstr_ref_prep                        false
% 7.24/1.48  --abstr_ref_until_sat                   false
% 7.24/1.48  --abstr_ref_sig_restrict                funpre
% 7.24/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.24/1.48  --abstr_ref_under                       []
% 7.24/1.48  
% 7.24/1.48  ------ SAT Options
% 7.24/1.48  
% 7.24/1.48  --sat_mode                              false
% 7.24/1.48  --sat_fm_restart_options                ""
% 7.24/1.48  --sat_gr_def                            false
% 7.24/1.48  --sat_epr_types                         true
% 7.24/1.48  --sat_non_cyclic_types                  false
% 7.24/1.48  --sat_finite_models                     false
% 7.24/1.48  --sat_fm_lemmas                         false
% 7.24/1.48  --sat_fm_prep                           false
% 7.24/1.48  --sat_fm_uc_incr                        true
% 7.24/1.48  --sat_out_model                         small
% 7.24/1.48  --sat_out_clauses                       false
% 7.24/1.48  
% 7.24/1.48  ------ QBF Options
% 7.24/1.48  
% 7.24/1.48  --qbf_mode                              false
% 7.24/1.48  --qbf_elim_univ                         false
% 7.24/1.48  --qbf_dom_inst                          none
% 7.24/1.48  --qbf_dom_pre_inst                      false
% 7.24/1.48  --qbf_sk_in                             false
% 7.24/1.48  --qbf_pred_elim                         true
% 7.24/1.48  --qbf_split                             512
% 7.24/1.48  
% 7.24/1.48  ------ BMC1 Options
% 7.24/1.48  
% 7.24/1.48  --bmc1_incremental                      false
% 7.24/1.48  --bmc1_axioms                           reachable_all
% 7.24/1.48  --bmc1_min_bound                        0
% 7.24/1.48  --bmc1_max_bound                        -1
% 7.24/1.48  --bmc1_max_bound_default                -1
% 7.24/1.48  --bmc1_symbol_reachability              true
% 7.24/1.48  --bmc1_property_lemmas                  false
% 7.24/1.48  --bmc1_k_induction                      false
% 7.24/1.48  --bmc1_non_equiv_states                 false
% 7.24/1.48  --bmc1_deadlock                         false
% 7.24/1.48  --bmc1_ucm                              false
% 7.24/1.48  --bmc1_add_unsat_core                   none
% 7.24/1.48  --bmc1_unsat_core_children              false
% 7.24/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.24/1.48  --bmc1_out_stat                         full
% 7.24/1.48  --bmc1_ground_init                      false
% 7.24/1.48  --bmc1_pre_inst_next_state              false
% 7.24/1.48  --bmc1_pre_inst_state                   false
% 7.24/1.48  --bmc1_pre_inst_reach_state             false
% 7.24/1.48  --bmc1_out_unsat_core                   false
% 7.24/1.48  --bmc1_aig_witness_out                  false
% 7.24/1.48  --bmc1_verbose                          false
% 7.24/1.48  --bmc1_dump_clauses_tptp                false
% 7.24/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.24/1.48  --bmc1_dump_file                        -
% 7.24/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.24/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.24/1.48  --bmc1_ucm_extend_mode                  1
% 7.24/1.48  --bmc1_ucm_init_mode                    2
% 7.24/1.48  --bmc1_ucm_cone_mode                    none
% 7.24/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.24/1.48  --bmc1_ucm_relax_model                  4
% 7.24/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.24/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.24/1.48  --bmc1_ucm_layered_model                none
% 7.24/1.48  --bmc1_ucm_max_lemma_size               10
% 7.24/1.48  
% 7.24/1.48  ------ AIG Options
% 7.24/1.48  
% 7.24/1.48  --aig_mode                              false
% 7.24/1.48  
% 7.24/1.48  ------ Instantiation Options
% 7.24/1.48  
% 7.24/1.48  --instantiation_flag                    true
% 7.24/1.48  --inst_sos_flag                         false
% 7.24/1.48  --inst_sos_phase                        true
% 7.24/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.24/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.24/1.48  --inst_lit_sel_side                     num_symb
% 7.24/1.48  --inst_solver_per_active                1400
% 7.24/1.48  --inst_solver_calls_frac                1.
% 7.24/1.48  --inst_passive_queue_type               priority_queues
% 7.24/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.24/1.48  --inst_passive_queues_freq              [25;2]
% 7.24/1.48  --inst_dismatching                      true
% 7.24/1.48  --inst_eager_unprocessed_to_passive     true
% 7.24/1.48  --inst_prop_sim_given                   true
% 7.24/1.48  --inst_prop_sim_new                     false
% 7.24/1.48  --inst_subs_new                         false
% 7.24/1.48  --inst_eq_res_simp                      false
% 7.24/1.48  --inst_subs_given                       false
% 7.24/1.48  --inst_orphan_elimination               true
% 7.24/1.48  --inst_learning_loop_flag               true
% 7.24/1.48  --inst_learning_start                   3000
% 7.24/1.48  --inst_learning_factor                  2
% 7.24/1.48  --inst_start_prop_sim_after_learn       3
% 7.24/1.48  --inst_sel_renew                        solver
% 7.24/1.48  --inst_lit_activity_flag                true
% 7.24/1.48  --inst_restr_to_given                   false
% 7.24/1.48  --inst_activity_threshold               500
% 7.24/1.48  --inst_out_proof                        true
% 7.24/1.48  
% 7.24/1.48  ------ Resolution Options
% 7.24/1.48  
% 7.24/1.48  --resolution_flag                       true
% 7.24/1.48  --res_lit_sel                           adaptive
% 7.24/1.48  --res_lit_sel_side                      none
% 7.24/1.48  --res_ordering                          kbo
% 7.24/1.48  --res_to_prop_solver                    active
% 7.24/1.48  --res_prop_simpl_new                    false
% 7.24/1.48  --res_prop_simpl_given                  true
% 7.24/1.48  --res_passive_queue_type                priority_queues
% 7.24/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.24/1.48  --res_passive_queues_freq               [15;5]
% 7.24/1.48  --res_forward_subs                      full
% 7.24/1.48  --res_backward_subs                     full
% 7.24/1.48  --res_forward_subs_resolution           true
% 7.24/1.48  --res_backward_subs_resolution          true
% 7.24/1.48  --res_orphan_elimination                true
% 7.24/1.48  --res_time_limit                        2.
% 7.24/1.48  --res_out_proof                         true
% 7.24/1.48  
% 7.24/1.48  ------ Superposition Options
% 7.24/1.48  
% 7.24/1.48  --superposition_flag                    true
% 7.24/1.48  --sup_passive_queue_type                priority_queues
% 7.24/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.24/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.24/1.48  --demod_completeness_check              fast
% 7.24/1.48  --demod_use_ground                      true
% 7.24/1.48  --sup_to_prop_solver                    passive
% 7.24/1.48  --sup_prop_simpl_new                    true
% 7.24/1.48  --sup_prop_simpl_given                  true
% 7.24/1.48  --sup_fun_splitting                     false
% 7.24/1.48  --sup_smt_interval                      50000
% 7.24/1.48  
% 7.24/1.48  ------ Superposition Simplification Setup
% 7.24/1.48  
% 7.24/1.48  --sup_indices_passive                   []
% 7.24/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.24/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.48  --sup_full_bw                           [BwDemod]
% 7.24/1.48  --sup_immed_triv                        [TrivRules]
% 7.24/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.24/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.48  --sup_immed_bw_main                     []
% 7.24/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.24/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.24/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.24/1.48  
% 7.24/1.48  ------ Combination Options
% 7.24/1.48  
% 7.24/1.48  --comb_res_mult                         3
% 7.24/1.48  --comb_sup_mult                         2
% 7.24/1.48  --comb_inst_mult                        10
% 7.24/1.48  
% 7.24/1.48  ------ Debug Options
% 7.24/1.48  
% 7.24/1.48  --dbg_backtrace                         false
% 7.24/1.48  --dbg_dump_prop_clauses                 false
% 7.24/1.48  --dbg_dump_prop_clauses_file            -
% 7.24/1.48  --dbg_out_stat                          false
% 7.24/1.48  ------ Parsing...
% 7.24/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.24/1.48  
% 7.24/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.24/1.48  
% 7.24/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.24/1.48  
% 7.24/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.24/1.48  ------ Proving...
% 7.24/1.48  ------ Problem Properties 
% 7.24/1.48  
% 7.24/1.48  
% 7.24/1.48  clauses                                 21
% 7.24/1.48  conjectures                             5
% 7.24/1.48  EPR                                     4
% 7.24/1.48  Horn                                    19
% 7.24/1.48  unary                                   5
% 7.24/1.48  binary                                  12
% 7.24/1.48  lits                                    42
% 7.24/1.48  lits eq                                 6
% 7.24/1.48  fd_pure                                 0
% 7.24/1.48  fd_pseudo                               0
% 7.24/1.48  fd_cond                                 0
% 7.24/1.48  fd_pseudo_cond                          0
% 7.24/1.48  AC symbols                              0
% 7.24/1.48  
% 7.24/1.48  ------ Schedule dynamic 5 is on 
% 7.24/1.48  
% 7.24/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.24/1.48  
% 7.24/1.48  
% 7.24/1.48  ------ 
% 7.24/1.48  Current options:
% 7.24/1.48  ------ 
% 7.24/1.48  
% 7.24/1.48  ------ Input Options
% 7.24/1.48  
% 7.24/1.48  --out_options                           all
% 7.24/1.48  --tptp_safe_out                         true
% 7.24/1.48  --problem_path                          ""
% 7.24/1.48  --include_path                          ""
% 7.24/1.48  --clausifier                            res/vclausify_rel
% 7.24/1.48  --clausifier_options                    --mode clausify
% 7.24/1.48  --stdin                                 false
% 7.24/1.48  --stats_out                             all
% 7.24/1.48  
% 7.24/1.48  ------ General Options
% 7.24/1.48  
% 7.24/1.48  --fof                                   false
% 7.24/1.48  --time_out_real                         305.
% 7.24/1.48  --time_out_virtual                      -1.
% 7.24/1.48  --symbol_type_check                     false
% 7.24/1.48  --clausify_out                          false
% 7.24/1.48  --sig_cnt_out                           false
% 7.24/1.48  --trig_cnt_out                          false
% 7.24/1.48  --trig_cnt_out_tolerance                1.
% 7.24/1.48  --trig_cnt_out_sk_spl                   false
% 7.24/1.48  --abstr_cl_out                          false
% 7.24/1.48  
% 7.24/1.48  ------ Global Options
% 7.24/1.48  
% 7.24/1.48  --schedule                              default
% 7.24/1.48  --add_important_lit                     false
% 7.24/1.48  --prop_solver_per_cl                    1000
% 7.24/1.48  --min_unsat_core                        false
% 7.24/1.48  --soft_assumptions                      false
% 7.24/1.48  --soft_lemma_size                       3
% 7.24/1.48  --prop_impl_unit_size                   0
% 7.24/1.48  --prop_impl_unit                        []
% 7.24/1.48  --share_sel_clauses                     true
% 7.24/1.48  --reset_solvers                         false
% 7.24/1.48  --bc_imp_inh                            [conj_cone]
% 7.24/1.48  --conj_cone_tolerance                   3.
% 7.24/1.48  --extra_neg_conj                        none
% 7.24/1.48  --large_theory_mode                     true
% 7.24/1.48  --prolific_symb_bound                   200
% 7.24/1.48  --lt_threshold                          2000
% 7.24/1.48  --clause_weak_htbl                      true
% 7.24/1.48  --gc_record_bc_elim                     false
% 7.24/1.48  
% 7.24/1.48  ------ Preprocessing Options
% 7.24/1.48  
% 7.24/1.48  --preprocessing_flag                    true
% 7.24/1.48  --time_out_prep_mult                    0.1
% 7.24/1.48  --splitting_mode                        input
% 7.24/1.48  --splitting_grd                         true
% 7.24/1.48  --splitting_cvd                         false
% 7.24/1.48  --splitting_cvd_svl                     false
% 7.24/1.48  --splitting_nvd                         32
% 7.24/1.48  --sub_typing                            true
% 7.24/1.48  --prep_gs_sim                           true
% 7.24/1.48  --prep_unflatten                        true
% 7.24/1.48  --prep_res_sim                          true
% 7.24/1.48  --prep_upred                            true
% 7.24/1.48  --prep_sem_filter                       exhaustive
% 7.24/1.48  --prep_sem_filter_out                   false
% 7.24/1.48  --pred_elim                             true
% 7.24/1.48  --res_sim_input                         true
% 7.24/1.48  --eq_ax_congr_red                       true
% 7.24/1.48  --pure_diseq_elim                       true
% 7.24/1.48  --brand_transform                       false
% 7.24/1.48  --non_eq_to_eq                          false
% 7.24/1.48  --prep_def_merge                        true
% 7.24/1.48  --prep_def_merge_prop_impl              false
% 7.24/1.48  --prep_def_merge_mbd                    true
% 7.24/1.48  --prep_def_merge_tr_red                 false
% 7.24/1.48  --prep_def_merge_tr_cl                  false
% 7.24/1.48  --smt_preprocessing                     true
% 7.24/1.48  --smt_ac_axioms                         fast
% 7.24/1.48  --preprocessed_out                      false
% 7.24/1.48  --preprocessed_stats                    false
% 7.24/1.48  
% 7.24/1.48  ------ Abstraction refinement Options
% 7.24/1.48  
% 7.24/1.48  --abstr_ref                             []
% 7.24/1.48  --abstr_ref_prep                        false
% 7.24/1.48  --abstr_ref_until_sat                   false
% 7.24/1.48  --abstr_ref_sig_restrict                funpre
% 7.24/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.24/1.48  --abstr_ref_under                       []
% 7.24/1.48  
% 7.24/1.48  ------ SAT Options
% 7.24/1.48  
% 7.24/1.48  --sat_mode                              false
% 7.24/1.48  --sat_fm_restart_options                ""
% 7.24/1.48  --sat_gr_def                            false
% 7.24/1.48  --sat_epr_types                         true
% 7.24/1.48  --sat_non_cyclic_types                  false
% 7.24/1.48  --sat_finite_models                     false
% 7.24/1.48  --sat_fm_lemmas                         false
% 7.24/1.48  --sat_fm_prep                           false
% 7.24/1.48  --sat_fm_uc_incr                        true
% 7.24/1.48  --sat_out_model                         small
% 7.24/1.48  --sat_out_clauses                       false
% 7.24/1.48  
% 7.24/1.48  ------ QBF Options
% 7.24/1.48  
% 7.24/1.48  --qbf_mode                              false
% 7.24/1.48  --qbf_elim_univ                         false
% 7.24/1.48  --qbf_dom_inst                          none
% 7.24/1.48  --qbf_dom_pre_inst                      false
% 7.24/1.48  --qbf_sk_in                             false
% 7.24/1.48  --qbf_pred_elim                         true
% 7.24/1.48  --qbf_split                             512
% 7.24/1.48  
% 7.24/1.48  ------ BMC1 Options
% 7.24/1.48  
% 7.24/1.48  --bmc1_incremental                      false
% 7.24/1.48  --bmc1_axioms                           reachable_all
% 7.24/1.48  --bmc1_min_bound                        0
% 7.24/1.48  --bmc1_max_bound                        -1
% 7.24/1.48  --bmc1_max_bound_default                -1
% 7.24/1.48  --bmc1_symbol_reachability              true
% 7.24/1.48  --bmc1_property_lemmas                  false
% 7.24/1.48  --bmc1_k_induction                      false
% 7.24/1.48  --bmc1_non_equiv_states                 false
% 7.24/1.48  --bmc1_deadlock                         false
% 7.24/1.48  --bmc1_ucm                              false
% 7.24/1.48  --bmc1_add_unsat_core                   none
% 7.24/1.48  --bmc1_unsat_core_children              false
% 7.24/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.24/1.48  --bmc1_out_stat                         full
% 7.24/1.48  --bmc1_ground_init                      false
% 7.24/1.48  --bmc1_pre_inst_next_state              false
% 7.24/1.48  --bmc1_pre_inst_state                   false
% 7.24/1.48  --bmc1_pre_inst_reach_state             false
% 7.24/1.48  --bmc1_out_unsat_core                   false
% 7.24/1.48  --bmc1_aig_witness_out                  false
% 7.24/1.48  --bmc1_verbose                          false
% 7.24/1.48  --bmc1_dump_clauses_tptp                false
% 7.24/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.24/1.48  --bmc1_dump_file                        -
% 7.24/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.24/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.24/1.48  --bmc1_ucm_extend_mode                  1
% 7.24/1.48  --bmc1_ucm_init_mode                    2
% 7.24/1.48  --bmc1_ucm_cone_mode                    none
% 7.24/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.24/1.48  --bmc1_ucm_relax_model                  4
% 7.24/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.24/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.24/1.48  --bmc1_ucm_layered_model                none
% 7.24/1.48  --bmc1_ucm_max_lemma_size               10
% 7.24/1.48  
% 7.24/1.48  ------ AIG Options
% 7.24/1.48  
% 7.24/1.48  --aig_mode                              false
% 7.24/1.48  
% 7.24/1.48  ------ Instantiation Options
% 7.24/1.48  
% 7.24/1.48  --instantiation_flag                    true
% 7.24/1.48  --inst_sos_flag                         false
% 7.24/1.48  --inst_sos_phase                        true
% 7.24/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.24/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.24/1.48  --inst_lit_sel_side                     none
% 7.24/1.48  --inst_solver_per_active                1400
% 7.24/1.48  --inst_solver_calls_frac                1.
% 7.24/1.48  --inst_passive_queue_type               priority_queues
% 7.24/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.24/1.48  --inst_passive_queues_freq              [25;2]
% 7.24/1.48  --inst_dismatching                      true
% 7.24/1.48  --inst_eager_unprocessed_to_passive     true
% 7.24/1.48  --inst_prop_sim_given                   true
% 7.24/1.48  --inst_prop_sim_new                     false
% 7.24/1.48  --inst_subs_new                         false
% 7.24/1.48  --inst_eq_res_simp                      false
% 7.24/1.48  --inst_subs_given                       false
% 7.24/1.48  --inst_orphan_elimination               true
% 7.24/1.48  --inst_learning_loop_flag               true
% 7.24/1.48  --inst_learning_start                   3000
% 7.24/1.48  --inst_learning_factor                  2
% 7.24/1.48  --inst_start_prop_sim_after_learn       3
% 7.24/1.48  --inst_sel_renew                        solver
% 7.24/1.48  --inst_lit_activity_flag                true
% 7.24/1.48  --inst_restr_to_given                   false
% 7.24/1.48  --inst_activity_threshold               500
% 7.24/1.48  --inst_out_proof                        true
% 7.24/1.48  
% 7.24/1.48  ------ Resolution Options
% 7.24/1.48  
% 7.24/1.48  --resolution_flag                       false
% 7.24/1.48  --res_lit_sel                           adaptive
% 7.24/1.48  --res_lit_sel_side                      none
% 7.24/1.48  --res_ordering                          kbo
% 7.24/1.48  --res_to_prop_solver                    active
% 7.24/1.48  --res_prop_simpl_new                    false
% 7.24/1.48  --res_prop_simpl_given                  true
% 7.24/1.48  --res_passive_queue_type                priority_queues
% 7.24/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.24/1.48  --res_passive_queues_freq               [15;5]
% 7.24/1.48  --res_forward_subs                      full
% 7.24/1.48  --res_backward_subs                     full
% 7.24/1.48  --res_forward_subs_resolution           true
% 7.24/1.48  --res_backward_subs_resolution          true
% 7.24/1.48  --res_orphan_elimination                true
% 7.24/1.48  --res_time_limit                        2.
% 7.24/1.48  --res_out_proof                         true
% 7.24/1.48  
% 7.24/1.48  ------ Superposition Options
% 7.24/1.48  
% 7.24/1.48  --superposition_flag                    true
% 7.24/1.48  --sup_passive_queue_type                priority_queues
% 7.24/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.24/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.24/1.48  --demod_completeness_check              fast
% 7.24/1.48  --demod_use_ground                      true
% 7.24/1.48  --sup_to_prop_solver                    passive
% 7.24/1.48  --sup_prop_simpl_new                    true
% 7.24/1.48  --sup_prop_simpl_given                  true
% 7.24/1.48  --sup_fun_splitting                     false
% 7.24/1.48  --sup_smt_interval                      50000
% 7.24/1.48  
% 7.24/1.48  ------ Superposition Simplification Setup
% 7.24/1.48  
% 7.24/1.48  --sup_indices_passive                   []
% 7.24/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.24/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.48  --sup_full_bw                           [BwDemod]
% 7.24/1.48  --sup_immed_triv                        [TrivRules]
% 7.24/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.24/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.48  --sup_immed_bw_main                     []
% 7.24/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.24/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.24/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.24/1.48  
% 7.24/1.48  ------ Combination Options
% 7.24/1.48  
% 7.24/1.48  --comb_res_mult                         3
% 7.24/1.48  --comb_sup_mult                         2
% 7.24/1.48  --comb_inst_mult                        10
% 7.24/1.48  
% 7.24/1.48  ------ Debug Options
% 7.24/1.48  
% 7.24/1.48  --dbg_backtrace                         false
% 7.24/1.48  --dbg_dump_prop_clauses                 false
% 7.24/1.48  --dbg_dump_prop_clauses_file            -
% 7.24/1.48  --dbg_out_stat                          false
% 7.24/1.48  
% 7.24/1.48  
% 7.24/1.48  
% 7.24/1.48  
% 7.24/1.48  ------ Proving...
% 7.24/1.48  
% 7.24/1.48  
% 7.24/1.48  % SZS status Theorem for theBenchmark.p
% 7.24/1.48  
% 7.24/1.48   Resolution empty clause
% 7.24/1.48  
% 7.24/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.24/1.48  
% 7.24/1.48  fof(f3,axiom,(
% 7.24/1.48    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 7.24/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.48  
% 7.24/1.48  fof(f36,plain,(
% 7.24/1.48    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 7.24/1.48    introduced(choice_axiom,[])).
% 7.24/1.48  
% 7.24/1.48  fof(f37,plain,(
% 7.24/1.48    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 7.24/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f3,f36])).
% 7.24/1.48  
% 7.24/1.48  fof(f49,plain,(
% 7.24/1.48    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 7.24/1.48    inference(cnf_transformation,[],[f37])).
% 7.24/1.48  
% 7.24/1.48  fof(f14,axiom,(
% 7.24/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 7.24/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.48  
% 7.24/1.48  fof(f32,plain,(
% 7.24/1.48    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.24/1.48    inference(ennf_transformation,[],[f14])).
% 7.24/1.48  
% 7.24/1.48  fof(f33,plain,(
% 7.24/1.48    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.24/1.48    inference(flattening,[],[f32])).
% 7.24/1.48  
% 7.24/1.48  fof(f61,plain,(
% 7.24/1.48    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.24/1.48    inference(cnf_transformation,[],[f33])).
% 7.24/1.48  
% 7.24/1.48  fof(f15,conjecture,(
% 7.24/1.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 7.24/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.48  
% 7.24/1.48  fof(f16,negated_conjecture,(
% 7.24/1.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 7.24/1.48    inference(negated_conjecture,[],[f15])).
% 7.24/1.48  
% 7.24/1.48  fof(f34,plain,(
% 7.24/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.24/1.48    inference(ennf_transformation,[],[f16])).
% 7.24/1.48  
% 7.24/1.48  fof(f35,plain,(
% 7.24/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.24/1.48    inference(flattening,[],[f34])).
% 7.24/1.48  
% 7.24/1.48  fof(f39,plain,(
% 7.24/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.24/1.48    inference(nnf_transformation,[],[f35])).
% 7.24/1.48  
% 7.24/1.48  fof(f40,plain,(
% 7.24/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.24/1.48    inference(flattening,[],[f39])).
% 7.24/1.48  
% 7.24/1.48  fof(f45,plain,(
% 7.24/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) => ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,sK5)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),sK5)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,sK5)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),sK5)) & m1_subset_1(sK5,k1_zfmisc_1(X1)))) )),
% 7.24/1.48    introduced(choice_axiom,[])).
% 7.24/1.48  
% 7.24/1.48  fof(f44,plain,(
% 7.24/1.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : ((~r1_tarski(sK4,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,sK4),X4)) & (r1_tarski(sK4,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,sK4),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(sK4,k1_zfmisc_1(X0)))) )),
% 7.24/1.48    introduced(choice_axiom,[])).
% 7.24/1.48  
% 7.24/1.48  fof(f43,plain,(
% 7.24/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,sK3,X4)) | ~r1_tarski(k7_relset_1(X0,X1,sK3,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,sK3,X4)) | r1_tarski(k7_relset_1(X0,X1,sK3,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK3,X0,X1) & v1_funct_1(sK3))) )),
% 7.24/1.48    introduced(choice_axiom,[])).
% 7.24/1.48  
% 7.24/1.48  fof(f42,plain,(
% 7.24/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,sK2,X2,X4)) | ~r1_tarski(k7_relset_1(X0,sK2,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,sK2,X2,X4)) | r1_tarski(k7_relset_1(X0,sK2,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK2))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_2(X2,X0,sK2) & v1_funct_1(X2)) & ~v1_xboole_0(sK2))) )),
% 7.24/1.48    introduced(choice_axiom,[])).
% 7.24/1.48  
% 7.24/1.48  fof(f41,plain,(
% 7.24/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK1,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK1,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK1,X1,X2,X4)) | r1_tarski(k7_relset_1(sK1,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) & v1_funct_2(X2,sK1,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 7.24/1.48    introduced(choice_axiom,[])).
% 7.24/1.48  
% 7.24/1.48  fof(f46,plain,(
% 7.24/1.48    (((((~r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) | ~r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)) & (r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) | r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 7.24/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f40,f45,f44,f43,f42,f41])).
% 7.24/1.48  
% 7.24/1.48  fof(f66,plain,(
% 7.24/1.48    v1_funct_2(sK3,sK1,sK2)),
% 7.24/1.48    inference(cnf_transformation,[],[f46])).
% 7.24/1.48  
% 7.24/1.48  fof(f65,plain,(
% 7.24/1.48    v1_funct_1(sK3)),
% 7.24/1.48    inference(cnf_transformation,[],[f46])).
% 7.24/1.48  
% 7.24/1.48  fof(f67,plain,(
% 7.24/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.24/1.48    inference(cnf_transformation,[],[f46])).
% 7.24/1.48  
% 7.24/1.48  fof(f13,axiom,(
% 7.24/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 7.24/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.48  
% 7.24/1.48  fof(f31,plain,(
% 7.24/1.48    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.24/1.48    inference(ennf_transformation,[],[f13])).
% 7.24/1.48  
% 7.24/1.48  fof(f60,plain,(
% 7.24/1.48    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.24/1.48    inference(cnf_transformation,[],[f31])).
% 7.24/1.48  
% 7.24/1.48  fof(f7,axiom,(
% 7.24/1.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 7.24/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.48  
% 7.24/1.48  fof(f23,plain,(
% 7.24/1.48    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.24/1.48    inference(ennf_transformation,[],[f7])).
% 7.24/1.48  
% 7.24/1.48  fof(f54,plain,(
% 7.24/1.48    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.24/1.48    inference(cnf_transformation,[],[f23])).
% 7.24/1.48  
% 7.24/1.48  fof(f11,axiom,(
% 7.24/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.24/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.48  
% 7.24/1.48  fof(f29,plain,(
% 7.24/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.24/1.48    inference(ennf_transformation,[],[f11])).
% 7.24/1.48  
% 7.24/1.48  fof(f58,plain,(
% 7.24/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.24/1.48    inference(cnf_transformation,[],[f29])).
% 7.24/1.48  
% 7.24/1.48  fof(f1,axiom,(
% 7.24/1.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.24/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.48  
% 7.24/1.48  fof(f17,plain,(
% 7.24/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.24/1.48    inference(ennf_transformation,[],[f1])).
% 7.24/1.48  
% 7.24/1.48  fof(f18,plain,(
% 7.24/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.24/1.48    inference(flattening,[],[f17])).
% 7.24/1.48  
% 7.24/1.48  fof(f47,plain,(
% 7.24/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.24/1.48    inference(cnf_transformation,[],[f18])).
% 7.24/1.48  
% 7.24/1.48  fof(f5,axiom,(
% 7.24/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.24/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.48  
% 7.24/1.48  fof(f38,plain,(
% 7.24/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.24/1.48    inference(nnf_transformation,[],[f5])).
% 7.24/1.48  
% 7.24/1.48  fof(f51,plain,(
% 7.24/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.24/1.48    inference(cnf_transformation,[],[f38])).
% 7.24/1.48  
% 7.24/1.48  fof(f68,plain,(
% 7.24/1.48    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 7.24/1.48    inference(cnf_transformation,[],[f46])).
% 7.24/1.48  
% 7.24/1.48  fof(f70,plain,(
% 7.24/1.48    r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) | r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)),
% 7.24/1.49    inference(cnf_transformation,[],[f46])).
% 7.24/1.49  
% 7.24/1.49  fof(f12,axiom,(
% 7.24/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.24/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.49  
% 7.24/1.49  fof(f30,plain,(
% 7.24/1.49    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.24/1.49    inference(ennf_transformation,[],[f12])).
% 7.24/1.49  
% 7.24/1.49  fof(f59,plain,(
% 7.24/1.49    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.24/1.49    inference(cnf_transformation,[],[f30])).
% 7.24/1.49  
% 7.24/1.49  fof(f9,axiom,(
% 7.24/1.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 7.24/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.49  
% 7.24/1.49  fof(f26,plain,(
% 7.24/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.24/1.49    inference(ennf_transformation,[],[f9])).
% 7.24/1.49  
% 7.24/1.49  fof(f27,plain,(
% 7.24/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.24/1.49    inference(flattening,[],[f26])).
% 7.24/1.49  
% 7.24/1.49  fof(f56,plain,(
% 7.24/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.24/1.49    inference(cnf_transformation,[],[f27])).
% 7.24/1.49  
% 7.24/1.49  fof(f71,plain,(
% 7.24/1.49    ~r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) | ~r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)),
% 7.24/1.49    inference(cnf_transformation,[],[f46])).
% 7.24/1.49  
% 7.24/1.49  fof(f6,axiom,(
% 7.24/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 7.24/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.49  
% 7.24/1.49  fof(f21,plain,(
% 7.24/1.49    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 7.24/1.49    inference(ennf_transformation,[],[f6])).
% 7.24/1.49  
% 7.24/1.49  fof(f22,plain,(
% 7.24/1.49    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 7.24/1.49    inference(flattening,[],[f21])).
% 7.24/1.49  
% 7.24/1.49  fof(f53,plain,(
% 7.24/1.49    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 7.24/1.49    inference(cnf_transformation,[],[f22])).
% 7.24/1.49  
% 7.24/1.49  fof(f8,axiom,(
% 7.24/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 7.24/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.49  
% 7.24/1.49  fof(f24,plain,(
% 7.24/1.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.24/1.49    inference(ennf_transformation,[],[f8])).
% 7.24/1.49  
% 7.24/1.49  fof(f25,plain,(
% 7.24/1.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.24/1.49    inference(flattening,[],[f24])).
% 7.24/1.49  
% 7.24/1.49  fof(f55,plain,(
% 7.24/1.49    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.24/1.49    inference(cnf_transformation,[],[f25])).
% 7.24/1.49  
% 7.24/1.49  fof(f4,axiom,(
% 7.24/1.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.24/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.49  
% 7.24/1.49  fof(f19,plain,(
% 7.24/1.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.24/1.49    inference(ennf_transformation,[],[f4])).
% 7.24/1.49  
% 7.24/1.49  fof(f20,plain,(
% 7.24/1.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.24/1.49    inference(flattening,[],[f19])).
% 7.24/1.49  
% 7.24/1.49  fof(f50,plain,(
% 7.24/1.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.24/1.49    inference(cnf_transformation,[],[f20])).
% 7.24/1.49  
% 7.24/1.49  fof(f10,axiom,(
% 7.24/1.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.24/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.49  
% 7.24/1.49  fof(f28,plain,(
% 7.24/1.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.24/1.49    inference(ennf_transformation,[],[f10])).
% 7.24/1.49  
% 7.24/1.49  fof(f57,plain,(
% 7.24/1.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.24/1.49    inference(cnf_transformation,[],[f28])).
% 7.24/1.49  
% 7.24/1.49  fof(f64,plain,(
% 7.24/1.49    ~v1_xboole_0(sK2)),
% 7.24/1.49    inference(cnf_transformation,[],[f46])).
% 7.24/1.49  
% 7.24/1.49  fof(f2,axiom,(
% 7.24/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.24/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.49  
% 7.24/1.49  fof(f48,plain,(
% 7.24/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.24/1.49    inference(cnf_transformation,[],[f2])).
% 7.24/1.49  
% 7.24/1.49  cnf(c_2,plain,
% 7.24/1.49      ( m1_subset_1(sK0(X0),X0) ),
% 7.24/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_2161,plain,
% 7.24/1.49      ( m1_subset_1(sK0(X0),X0) = iProver_top ),
% 7.24/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_15,plain,
% 7.24/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.24/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.24/1.49      | ~ v1_funct_1(X0)
% 7.24/1.49      | k8_relset_1(X1,X2,X0,X2) = X1
% 7.24/1.49      | k1_xboole_0 = X2 ),
% 7.24/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_21,negated_conjecture,
% 7.24/1.49      ( v1_funct_2(sK3,sK1,sK2) ),
% 7.24/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_399,plain,
% 7.24/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.24/1.49      | ~ v1_funct_1(X0)
% 7.24/1.49      | k8_relset_1(X1,X2,X0,X2) = X1
% 7.24/1.49      | sK3 != X0
% 7.24/1.49      | sK2 != X2
% 7.24/1.49      | sK1 != X1
% 7.24/1.49      | k1_xboole_0 = X2 ),
% 7.24/1.49      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_400,plain,
% 7.24/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.24/1.49      | ~ v1_funct_1(sK3)
% 7.24/1.49      | k8_relset_1(sK1,sK2,sK3,sK2) = sK1
% 7.24/1.49      | k1_xboole_0 = sK2 ),
% 7.24/1.49      inference(unflattening,[status(thm)],[c_399]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_22,negated_conjecture,
% 7.24/1.49      ( v1_funct_1(sK3) ),
% 7.24/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_20,negated_conjecture,
% 7.24/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.24/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_402,plain,
% 7.24/1.49      ( k8_relset_1(sK1,sK2,sK3,sK2) = sK1 | k1_xboole_0 = sK2 ),
% 7.24/1.49      inference(global_propositional_subsumption,
% 7.24/1.49                [status(thm)],
% 7.24/1.49                [c_400,c_22,c_20]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_2149,plain,
% 7.24/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.24/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_13,plain,
% 7.24/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.24/1.49      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 7.24/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_2154,plain,
% 7.24/1.49      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 7.24/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.24/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_3195,plain,
% 7.24/1.49      ( k8_relset_1(sK1,sK2,sK3,X0) = k10_relat_1(sK3,X0) ),
% 7.24/1.49      inference(superposition,[status(thm)],[c_2149,c_2154]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_3786,plain,
% 7.24/1.49      ( k10_relat_1(sK3,sK2) = sK1 | sK2 = k1_xboole_0 ),
% 7.24/1.49      inference(superposition,[status(thm)],[c_402,c_3195]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_7,plain,
% 7.24/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.24/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_2157,plain,
% 7.24/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 7.24/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.24/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_4021,plain,
% 7.24/1.49      ( sK2 = k1_xboole_0
% 7.24/1.49      | r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
% 7.24/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.24/1.49      inference(superposition,[status(thm)],[c_3786,c_2157]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_29,plain,
% 7.24/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.24/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_11,plain,
% 7.24/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.24/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_2334,plain,
% 7.24/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.24/1.49      | v1_relat_1(sK3) ),
% 7.24/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_2335,plain,
% 7.24/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.24/1.49      | v1_relat_1(sK3) = iProver_top ),
% 7.24/1.49      inference(predicate_to_equality,[status(thm)],[c_2334]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_5885,plain,
% 7.24/1.49      ( r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top | sK2 = k1_xboole_0 ),
% 7.24/1.49      inference(global_propositional_subsumption,
% 7.24/1.49                [status(thm)],
% 7.24/1.49                [c_4021,c_29,c_2335]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_5886,plain,
% 7.24/1.49      ( sK2 = k1_xboole_0 | r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top ),
% 7.24/1.49      inference(renaming,[status(thm)],[c_5885]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_0,plain,
% 7.24/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 7.24/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_2163,plain,
% 7.24/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.24/1.49      | r1_tarski(X2,X0) != iProver_top
% 7.24/1.49      | r1_tarski(X2,X1) = iProver_top ),
% 7.24/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_5891,plain,
% 7.24/1.49      ( sK2 = k1_xboole_0
% 7.24/1.49      | r1_tarski(X0,k1_relat_1(sK3)) = iProver_top
% 7.24/1.49      | r1_tarski(X0,sK1) != iProver_top ),
% 7.24/1.49      inference(superposition,[status(thm)],[c_5886,c_2163]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_7550,plain,
% 7.24/1.49      ( sK2 = k1_xboole_0
% 7.24/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.24/1.49      | r1_tarski(X0,k1_relat_1(sK3)) = iProver_top
% 7.24/1.49      | r1_tarski(X1,sK1) != iProver_top ),
% 7.24/1.49      inference(superposition,[status(thm)],[c_5891,c_2163]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_5,plain,
% 7.24/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.24/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_189,plain,
% 7.24/1.49      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.24/1.49      inference(prop_impl,[status(thm)],[c_5]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_190,plain,
% 7.24/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.24/1.49      inference(renaming,[status(thm)],[c_189]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_19,negated_conjecture,
% 7.24/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 7.24/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_634,plain,
% 7.24/1.49      ( r1_tarski(X0,X1) | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1) | sK4 != X0 ),
% 7.24/1.49      inference(resolution_lifted,[status(thm)],[c_190,c_19]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_635,plain,
% 7.24/1.49      ( r1_tarski(sK4,X0) | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 7.24/1.49      inference(unflattening,[status(thm)],[c_634]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_636,plain,
% 7.24/1.49      ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) | r1_tarski(sK4,X0) = iProver_top ),
% 7.24/1.49      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_638,plain,
% 7.24/1.49      ( k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
% 7.24/1.49      | r1_tarski(sK4,sK1) = iProver_top ),
% 7.24/1.49      inference(instantiation,[status(thm)],[c_636]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_1642,plain,
% 7.24/1.49      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 7.24/1.49      theory(equality) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_1652,plain,
% 7.24/1.49      ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) | sK1 != sK1 ),
% 7.24/1.49      inference(instantiation,[status(thm)],[c_1642]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_1638,plain,( X0 = X0 ),theory(equality) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_1661,plain,
% 7.24/1.49      ( sK1 = sK1 ),
% 7.24/1.49      inference(instantiation,[status(thm)],[c_1638]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_17,negated_conjecture,
% 7.24/1.49      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)
% 7.24/1.49      | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) ),
% 7.24/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_2152,plain,
% 7.24/1.49      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) = iProver_top
% 7.24/1.49      | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) = iProver_top ),
% 7.24/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_3774,plain,
% 7.24/1.49      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) = iProver_top
% 7.24/1.49      | r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top ),
% 7.24/1.49      inference(demodulation,[status(thm)],[c_3195,c_2152]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_12,plain,
% 7.24/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.24/1.49      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.24/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_2155,plain,
% 7.24/1.49      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.24/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.24/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_3482,plain,
% 7.24/1.49      ( k7_relset_1(sK1,sK2,sK3,X0) = k9_relat_1(sK3,X0) ),
% 7.24/1.49      inference(superposition,[status(thm)],[c_2149,c_2155]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_4179,plain,
% 7.24/1.49      ( r1_tarski(k9_relat_1(sK3,sK4),sK5) = iProver_top
% 7.24/1.49      | r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top ),
% 7.24/1.49      inference(demodulation,[status(thm)],[c_3774,c_3482]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_9,plain,
% 7.24/1.49      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 7.24/1.49      | ~ r1_tarski(X0,k1_relat_1(X1))
% 7.24/1.49      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 7.24/1.49      | ~ v1_funct_1(X1)
% 7.24/1.49      | ~ v1_relat_1(X1) ),
% 7.24/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_428,plain,
% 7.24/1.49      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 7.24/1.49      | ~ r1_tarski(X0,k1_relat_1(X1))
% 7.24/1.49      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 7.24/1.49      | ~ v1_relat_1(X1)
% 7.24/1.49      | sK3 != X1 ),
% 7.24/1.49      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_429,plain,
% 7.24/1.49      ( r1_tarski(X0,k10_relat_1(sK3,X1))
% 7.24/1.49      | ~ r1_tarski(X0,k1_relat_1(sK3))
% 7.24/1.49      | ~ r1_tarski(k9_relat_1(sK3,X0),X1)
% 7.24/1.49      | ~ v1_relat_1(sK3) ),
% 7.24/1.49      inference(unflattening,[status(thm)],[c_428]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_2144,plain,
% 7.24/1.49      ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
% 7.24/1.49      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 7.24/1.49      | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
% 7.24/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.24/1.49      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_430,plain,
% 7.24/1.49      ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
% 7.24/1.49      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 7.24/1.49      | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
% 7.24/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.24/1.49      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_2550,plain,
% 7.24/1.49      ( r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
% 7.24/1.49      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 7.24/1.49      | r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top ),
% 7.24/1.49      inference(global_propositional_subsumption,
% 7.24/1.49                [status(thm)],
% 7.24/1.49                [c_2144,c_29,c_430,c_2335]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_2551,plain,
% 7.24/1.49      ( r1_tarski(X0,k10_relat_1(sK3,X1)) = iProver_top
% 7.24/1.49      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 7.24/1.49      | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top ),
% 7.24/1.49      inference(renaming,[status(thm)],[c_2550]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_4184,plain,
% 7.24/1.49      ( r1_tarski(sK4,k10_relat_1(sK3,sK5)) = iProver_top
% 7.24/1.49      | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
% 7.24/1.49      inference(superposition,[status(thm)],[c_4179,c_2551]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_5021,plain,
% 7.24/1.49      ( r1_tarski(X0,k10_relat_1(sK3,sK5)) = iProver_top
% 7.24/1.49      | r1_tarski(X0,sK4) != iProver_top
% 7.24/1.49      | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
% 7.24/1.49      inference(superposition,[status(thm)],[c_4184,c_2163]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_12355,plain,
% 7.24/1.49      ( r1_tarski(X0,k10_relat_1(sK3,k10_relat_1(sK3,sK5))) = iProver_top
% 7.24/1.49      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 7.24/1.49      | r1_tarski(k9_relat_1(sK3,X0),sK4) != iProver_top
% 7.24/1.49      | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
% 7.24/1.49      inference(superposition,[status(thm)],[c_5021,c_2551]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_16,negated_conjecture,
% 7.24/1.49      ( ~ r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5)
% 7.24/1.49      | ~ r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) ),
% 7.24/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_2153,plain,
% 7.24/1.49      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) != iProver_top
% 7.24/1.49      | r1_tarski(sK4,k8_relset_1(sK1,sK2,sK3,sK5)) != iProver_top ),
% 7.24/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_3775,plain,
% 7.24/1.49      ( r1_tarski(k7_relset_1(sK1,sK2,sK3,sK4),sK5) != iProver_top
% 7.24/1.49      | r1_tarski(sK4,k10_relat_1(sK3,sK5)) != iProver_top ),
% 7.24/1.49      inference(demodulation,[status(thm)],[c_3195,c_2153]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_4015,plain,
% 7.24/1.49      ( r1_tarski(k9_relat_1(sK3,sK4),sK5) != iProver_top
% 7.24/1.49      | r1_tarski(sK4,k10_relat_1(sK3,sK5)) != iProver_top ),
% 7.24/1.49      inference(demodulation,[status(thm)],[c_3775,c_3482]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_5022,plain,
% 7.24/1.49      ( r1_tarski(k9_relat_1(sK3,sK4),sK5) != iProver_top
% 7.24/1.49      | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
% 7.24/1.49      inference(superposition,[status(thm)],[c_4184,c_4015]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_6,plain,
% 7.24/1.49      ( ~ r1_tarski(X0,X1)
% 7.24/1.49      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 7.24/1.49      | ~ v1_relat_1(X2) ),
% 7.24/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_2158,plain,
% 7.24/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.24/1.49      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
% 7.24/1.49      | v1_relat_1(X2) != iProver_top ),
% 7.24/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_8,plain,
% 7.24/1.49      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 7.24/1.49      | ~ v1_funct_1(X0)
% 7.24/1.49      | ~ v1_relat_1(X0) ),
% 7.24/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_416,plain,
% 7.24/1.49      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 7.24/1.49      | ~ v1_relat_1(X0)
% 7.24/1.49      | sK3 != X0 ),
% 7.24/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_417,plain,
% 7.24/1.49      ( r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,X0)),X0) | ~ v1_relat_1(sK3) ),
% 7.24/1.49      inference(unflattening,[status(thm)],[c_416]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_2145,plain,
% 7.24/1.49      ( r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,X0)),X0) = iProver_top
% 7.24/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.24/1.49      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_418,plain,
% 7.24/1.49      ( r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,X0)),X0) = iProver_top
% 7.24/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.24/1.49      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_3014,plain,
% 7.24/1.49      ( r1_tarski(k9_relat_1(sK3,k10_relat_1(sK3,X0)),X0) = iProver_top ),
% 7.24/1.49      inference(global_propositional_subsumption,
% 7.24/1.49                [status(thm)],
% 7.24/1.49                [c_2145,c_29,c_418,c_2335]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_3538,plain,
% 7.24/1.49      ( r1_tarski(X0,X1) = iProver_top
% 7.24/1.49      | r1_tarski(X0,k9_relat_1(sK3,k10_relat_1(sK3,X1))) != iProver_top ),
% 7.24/1.49      inference(superposition,[status(thm)],[c_3014,c_2163]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_5215,plain,
% 7.24/1.49      ( r1_tarski(X0,k10_relat_1(sK3,X1)) != iProver_top
% 7.24/1.49      | r1_tarski(k9_relat_1(sK3,X0),X1) = iProver_top
% 7.24/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.24/1.49      inference(superposition,[status(thm)],[c_2158,c_3538]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_12431,plain,
% 7.24/1.49      ( r1_tarski(k9_relat_1(sK3,X0),X1) = iProver_top
% 7.24/1.49      | r1_tarski(X0,k10_relat_1(sK3,X1)) != iProver_top ),
% 7.24/1.49      inference(global_propositional_subsumption,
% 7.24/1.49                [status(thm)],
% 7.24/1.49                [c_5215,c_29,c_2335]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_12432,plain,
% 7.24/1.49      ( r1_tarski(X0,k10_relat_1(sK3,X1)) != iProver_top
% 7.24/1.49      | r1_tarski(k9_relat_1(sK3,X0),X1) = iProver_top ),
% 7.24/1.49      inference(renaming,[status(thm)],[c_12431]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_12445,plain,
% 7.24/1.49      ( r1_tarski(k9_relat_1(sK3,sK4),sK5) = iProver_top
% 7.24/1.49      | r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
% 7.24/1.49      inference(superposition,[status(thm)],[c_4184,c_12432]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_13112,plain,
% 7.24/1.49      ( r1_tarski(sK4,k1_relat_1(sK3)) != iProver_top ),
% 7.24/1.49      inference(global_propositional_subsumption,
% 7.24/1.49                [status(thm)],
% 7.24/1.49                [c_12355,c_5022,c_12445]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_13117,plain,
% 7.24/1.49      ( sK2 = k1_xboole_0 | r1_tarski(sK4,sK1) != iProver_top ),
% 7.24/1.49      inference(superposition,[status(thm)],[c_5891,c_13112]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_22376,plain,
% 7.24/1.49      ( sK2 = k1_xboole_0 ),
% 7.24/1.49      inference(global_propositional_subsumption,
% 7.24/1.49                [status(thm)],
% 7.24/1.49                [c_7550,c_638,c_1652,c_1661,c_13117]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_3,plain,
% 7.24/1.49      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 7.24/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_10,plain,
% 7.24/1.49      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.24/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_334,plain,
% 7.24/1.49      ( ~ m1_subset_1(X0,X1) | ~ r1_tarski(X1,X0) | v1_xboole_0(X1) ),
% 7.24/1.49      inference(resolution,[status(thm)],[c_3,c_10]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_23,negated_conjecture,
% 7.24/1.49      ( ~ v1_xboole_0(sK2) ),
% 7.24/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_352,plain,
% 7.24/1.49      ( ~ m1_subset_1(X0,X1) | ~ r1_tarski(X1,X0) | sK2 != X1 ),
% 7.24/1.49      inference(resolution_lifted,[status(thm)],[c_334,c_23]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_353,plain,
% 7.24/1.49      ( ~ m1_subset_1(X0,sK2) | ~ r1_tarski(sK2,X0) ),
% 7.24/1.49      inference(unflattening,[status(thm)],[c_352]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_2148,plain,
% 7.24/1.49      ( m1_subset_1(X0,sK2) != iProver_top | r1_tarski(sK2,X0) != iProver_top ),
% 7.24/1.49      inference(predicate_to_equality,[status(thm)],[c_353]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_22433,plain,
% 7.24/1.49      ( m1_subset_1(X0,k1_xboole_0) != iProver_top
% 7.24/1.49      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 7.24/1.49      inference(demodulation,[status(thm)],[c_22376,c_2148]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_1,plain,
% 7.24/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.24/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_76,plain,
% 7.24/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.24/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_25207,plain,
% 7.24/1.49      ( m1_subset_1(X0,k1_xboole_0) != iProver_top ),
% 7.24/1.49      inference(global_propositional_subsumption,[status(thm)],[c_22433,c_76]) ).
% 7.24/1.49  
% 7.24/1.49  cnf(c_25214,plain,
% 7.24/1.49      ( $false ),
% 7.24/1.49      inference(superposition,[status(thm)],[c_2161,c_25207]) ).
% 7.24/1.49  
% 7.24/1.49  
% 7.24/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.24/1.49  
% 7.24/1.49  ------                               Statistics
% 7.24/1.49  
% 7.24/1.49  ------ General
% 7.24/1.49  
% 7.24/1.49  abstr_ref_over_cycles:                  0
% 7.24/1.49  abstr_ref_under_cycles:                 0
% 7.24/1.49  gc_basic_clause_elim:                   0
% 7.24/1.49  forced_gc_time:                         0
% 7.24/1.49  parsing_time:                           0.008
% 7.24/1.49  unif_index_cands_time:                  0.
% 7.24/1.49  unif_index_add_time:                    0.
% 7.24/1.49  orderings_time:                         0.
% 7.24/1.49  out_proof_time:                         0.014
% 7.24/1.49  total_time:                             0.668
% 7.24/1.49  num_of_symbols:                         52
% 7.24/1.49  num_of_terms:                           22174
% 7.24/1.49  
% 7.24/1.49  ------ Preprocessing
% 7.24/1.49  
% 7.24/1.49  num_of_splits:                          0
% 7.24/1.49  num_of_split_atoms:                     0
% 7.24/1.49  num_of_reused_defs:                     0
% 7.24/1.49  num_eq_ax_congr_red:                    12
% 7.24/1.49  num_of_sem_filtered_clauses:            1
% 7.24/1.49  num_of_subtypes:                        1
% 7.24/1.49  monotx_restored_types:                  0
% 7.24/1.49  sat_num_of_epr_types:                   0
% 7.24/1.49  sat_num_of_non_cyclic_types:            0
% 7.24/1.49  sat_guarded_non_collapsed_types:        0
% 7.24/1.49  num_pure_diseq_elim:                    0
% 7.24/1.49  simp_replaced_by:                       0
% 7.24/1.49  res_preprocessed:                       113
% 7.24/1.49  prep_upred:                             0
% 7.24/1.49  prep_unflattend:                        89
% 7.24/1.49  smt_new_axioms:                         0
% 7.24/1.49  pred_elim_cands:                        3
% 7.24/1.49  pred_elim:                              4
% 7.24/1.49  pred_elim_cl:                           4
% 7.24/1.49  pred_elim_cycles:                       8
% 7.24/1.49  merged_defs:                            16
% 7.24/1.49  merged_defs_ncl:                        0
% 7.24/1.49  bin_hyper_res:                          16
% 7.24/1.49  prep_cycles:                            4
% 7.24/1.49  pred_elim_time:                         0.018
% 7.24/1.49  splitting_time:                         0.
% 7.24/1.49  sem_filter_time:                        0.
% 7.24/1.49  monotx_time:                            0.
% 7.24/1.49  subtype_inf_time:                       0.
% 7.24/1.49  
% 7.24/1.49  ------ Problem properties
% 7.24/1.49  
% 7.24/1.49  clauses:                                21
% 7.24/1.49  conjectures:                            5
% 7.24/1.49  epr:                                    4
% 7.24/1.49  horn:                                   19
% 7.24/1.49  ground:                                 7
% 7.24/1.49  unary:                                  5
% 7.24/1.49  binary:                                 12
% 7.24/1.49  lits:                                   42
% 7.24/1.49  lits_eq:                                6
% 7.24/1.49  fd_pure:                                0
% 7.24/1.49  fd_pseudo:                              0
% 7.24/1.49  fd_cond:                                0
% 7.24/1.49  fd_pseudo_cond:                         0
% 7.24/1.49  ac_symbols:                             0
% 7.24/1.49  
% 7.24/1.49  ------ Propositional Solver
% 7.24/1.49  
% 7.24/1.49  prop_solver_calls:                      30
% 7.24/1.49  prop_fast_solver_calls:                 1279
% 7.24/1.49  smt_solver_calls:                       0
% 7.24/1.49  smt_fast_solver_calls:                  0
% 7.24/1.49  prop_num_of_clauses:                    8930
% 7.24/1.49  prop_preprocess_simplified:             18843
% 7.24/1.49  prop_fo_subsumed:                       21
% 7.24/1.49  prop_solver_time:                       0.
% 7.24/1.49  smt_solver_time:                        0.
% 7.24/1.49  smt_fast_solver_time:                   0.
% 7.24/1.49  prop_fast_solver_time:                  0.
% 7.24/1.49  prop_unsat_core_time:                   0.
% 7.24/1.49  
% 7.24/1.49  ------ QBF
% 7.24/1.49  
% 7.24/1.49  qbf_q_res:                              0
% 7.24/1.49  qbf_num_tautologies:                    0
% 7.24/1.49  qbf_prep_cycles:                        0
% 7.24/1.49  
% 7.24/1.49  ------ BMC1
% 7.24/1.49  
% 7.24/1.49  bmc1_current_bound:                     -1
% 7.24/1.49  bmc1_last_solved_bound:                 -1
% 7.24/1.49  bmc1_unsat_core_size:                   -1
% 7.24/1.49  bmc1_unsat_core_parents_size:           -1
% 7.24/1.49  bmc1_merge_next_fun:                    0
% 7.24/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.24/1.49  
% 7.24/1.49  ------ Instantiation
% 7.24/1.49  
% 7.24/1.49  inst_num_of_clauses:                    2455
% 7.24/1.49  inst_num_in_passive:                    1758
% 7.24/1.49  inst_num_in_active:                     651
% 7.24/1.49  inst_num_in_unprocessed:                46
% 7.24/1.49  inst_num_of_loops:                      790
% 7.24/1.49  inst_num_of_learning_restarts:          0
% 7.24/1.49  inst_num_moves_active_passive:          138
% 7.24/1.49  inst_lit_activity:                      0
% 7.24/1.49  inst_lit_activity_moves:                1
% 7.24/1.49  inst_num_tautologies:                   0
% 7.24/1.49  inst_num_prop_implied:                  0
% 7.24/1.49  inst_num_existing_simplified:           0
% 7.24/1.49  inst_num_eq_res_simplified:             0
% 7.24/1.49  inst_num_child_elim:                    0
% 7.24/1.49  inst_num_of_dismatching_blockings:      2018
% 7.24/1.49  inst_num_of_non_proper_insts:           1450
% 7.24/1.49  inst_num_of_duplicates:                 0
% 7.24/1.49  inst_inst_num_from_inst_to_res:         0
% 7.24/1.49  inst_dismatching_checking_time:         0.
% 7.24/1.49  
% 7.24/1.49  ------ Resolution
% 7.24/1.49  
% 7.24/1.49  res_num_of_clauses:                     0
% 7.24/1.49  res_num_in_passive:                     0
% 7.24/1.49  res_num_in_active:                      0
% 7.24/1.49  res_num_of_loops:                       117
% 7.24/1.49  res_forward_subset_subsumed:            85
% 7.24/1.49  res_backward_subset_subsumed:           0
% 7.24/1.49  res_forward_subsumed:                   0
% 7.24/1.49  res_backward_subsumed:                  0
% 7.24/1.49  res_forward_subsumption_resolution:     0
% 7.24/1.49  res_backward_subsumption_resolution:    0
% 7.24/1.49  res_clause_to_clause_subsumption:       4321
% 7.24/1.49  res_orphan_elimination:                 0
% 7.24/1.49  res_tautology_del:                      119
% 7.24/1.49  res_num_eq_res_simplified:              0
% 7.24/1.49  res_num_sel_changes:                    0
% 7.24/1.49  res_moves_from_active_to_pass:          0
% 7.24/1.49  
% 7.24/1.49  ------ Superposition
% 7.24/1.49  
% 7.24/1.49  sup_time_total:                         0.
% 7.24/1.49  sup_time_generating:                    0.
% 7.24/1.49  sup_time_sim_full:                      0.
% 7.24/1.49  sup_time_sim_immed:                     0.
% 7.24/1.49  
% 7.24/1.49  sup_num_of_clauses:                     485
% 7.24/1.49  sup_num_in_active:                      94
% 7.24/1.49  sup_num_in_passive:                     391
% 7.24/1.49  sup_num_of_loops:                       157
% 7.24/1.49  sup_fw_superposition:                   379
% 7.24/1.49  sup_bw_superposition:                   451
% 7.24/1.49  sup_immediate_simplified:               145
% 7.24/1.49  sup_given_eliminated:                   1
% 7.24/1.49  comparisons_done:                       0
% 7.24/1.49  comparisons_avoided:                    3
% 7.24/1.49  
% 7.24/1.49  ------ Simplifications
% 7.24/1.49  
% 7.24/1.49  
% 7.24/1.49  sim_fw_subset_subsumed:                 29
% 7.24/1.49  sim_bw_subset_subsumed:                 27
% 7.24/1.49  sim_fw_subsumed:                        114
% 7.24/1.49  sim_bw_subsumed:                        2
% 7.24/1.49  sim_fw_subsumption_res:                 0
% 7.24/1.49  sim_bw_subsumption_res:                 1
% 7.24/1.49  sim_tautology_del:                      53
% 7.24/1.49  sim_eq_tautology_del:                   2
% 7.24/1.49  sim_eq_res_simp:                        0
% 7.24/1.49  sim_fw_demodulated:                     3
% 7.24/1.49  sim_bw_demodulated:                     60
% 7.24/1.49  sim_light_normalised:                   0
% 7.24/1.49  sim_joinable_taut:                      0
% 7.24/1.49  sim_joinable_simp:                      0
% 7.24/1.49  sim_ac_normalised:                      0
% 7.24/1.49  sim_smt_subsumption:                    0
% 7.24/1.49  
%------------------------------------------------------------------------------

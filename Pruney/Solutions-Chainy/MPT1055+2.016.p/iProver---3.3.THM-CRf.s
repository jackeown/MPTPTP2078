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
% DateTime   : Thu Dec  3 12:09:10 EST 2020

% Result     : Theorem 11.83s
% Output     : CNFRefutation 11.83s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 610 expanded)
%              Number of clauses        :   76 ( 165 expanded)
%              Number of leaves         :   21 ( 191 expanded)
%              Depth                    :   17
%              Number of atoms          :  473 (4560 expanded)
%              Number of equality atoms :  130 ( 222 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
            | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
          & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
            | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
     => ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,sK4))
          | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),sK4) )
        & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,sK4))
          | r1_tarski(k7_relset_1(X0,X1,X2,X3),sK4) )
        & m1_subset_1(sK4,k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
            ( ( ~ r1_tarski(sK3,k8_relset_1(X0,X1,X2,X4))
              | ~ r1_tarski(k7_relset_1(X0,X1,X2,sK3),X4) )
            & ( r1_tarski(sK3,k8_relset_1(X0,X1,X2,X4))
              | r1_tarski(k7_relset_1(X0,X1,X2,sK3),X4) )
            & m1_subset_1(X4,k1_zfmisc_1(X1)) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
                ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,sK2,X4))
                  | ~ r1_tarski(k7_relset_1(X0,X1,sK2,X3),X4) )
                & ( r1_tarski(X3,k8_relset_1(X0,X1,sK2,X4))
                  | r1_tarski(k7_relset_1(X0,X1,sK2,X3),X4) )
                & m1_subset_1(X4,k1_zfmisc_1(X1)) )
            & m1_subset_1(X3,k1_zfmisc_1(X0)) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK2,X0,X1)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
                    ( ( ~ r1_tarski(X3,k8_relset_1(X0,sK1,X2,X4))
                      | ~ r1_tarski(k7_relset_1(X0,sK1,X2,X3),X4) )
                    & ( r1_tarski(X3,k8_relset_1(X0,sK1,X2,X4))
                      | r1_tarski(k7_relset_1(X0,sK1,X2,X3),X4) )
                    & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
            & v1_funct_2(X2,X0,sK1)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
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
                      ( ( ~ r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
              & v1_funct_2(X2,sK0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
      | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
    & ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
      | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f44,f49,f48,f47,f46,f45])).

fof(f78,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1276,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1287,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2528,plain,
    ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1276,c_1287])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,X1)
    | r1_tarski(X3,k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X3)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1281,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X3,k8_relset_1(X2,X0,X1,k7_relset_1(X2,X0,X1,X3))) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4778,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(X0,k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,X0))) = iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2528,c_1281])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_35,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_567,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1542,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_567])).

cnf(c_38529,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1542])).

cnf(c_42245,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(X0,k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4778,c_30,c_34,c_35,c_36,c_0,c_38529])).

cnf(c_42246,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,X0))) = iProver_top
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_42245])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1288,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2543,plain,
    ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1276,c_1288])).

cnf(c_42251,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) = iProver_top
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_42246,c_2543])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1277,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1294,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1949,plain,
    ( r1_tarski(sK3,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1277,c_1294])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1296,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4063,plain,
    ( r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1949,c_1296])).

cnf(c_42288,plain,
    ( r1_tarski(sK0,sK0) != iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_42251,c_4063])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1284,plain,
    ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3545,plain,
    ( k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) = k1_relset_1(sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1276,c_1284])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1289,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2364,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1276,c_1289])).

cnf(c_6939,plain,
    ( k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3545,c_2364])).

cnf(c_6940,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_6939,c_2528,c_2543])).

cnf(c_42371,plain,
    ( r1_tarski(sK0,sK0) != iProver_top
    | r1_tarski(sK3,k1_relat_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_42288,c_6940])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1279,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4767,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2528,c_1279])).

cnf(c_8050,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4767,c_2543])).

cnf(c_13,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1290,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8058,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top
    | r1_tarski(sK3,k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8050,c_1290])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_212,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_213,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_212])).

cnf(c_271,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_213])).

cnf(c_1719,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[status(thm)],[c_8,c_27])).

cnf(c_2146,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_271,c_1719])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2402,plain,
    ( v1_relat_1(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2146,c_10])).

cnf(c_2403,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2402])).

cnf(c_16588,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top
    | r1_tarski(sK3,k1_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8058,c_34,c_2403])).

cnf(c_12,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1291,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1292,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3366,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(X2,X1),X3) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),X3) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1292,c_1296])).

cnf(c_18051,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1291,c_3366])).

cnf(c_18703,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_16588,c_18051])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1280,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4766,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2528,c_1280])).

cnf(c_9375,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4766,c_2543])).

cnf(c_16601,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK3,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16588,c_9375])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_94,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_96,plain,
    ( r1_tarski(sK0,sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_42371,c_18703,c_16601,c_2403,c_96,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.83/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.83/2.00  
% 11.83/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.83/2.00  
% 11.83/2.00  ------  iProver source info
% 11.83/2.00  
% 11.83/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.83/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.83/2.00  git: non_committed_changes: false
% 11.83/2.00  git: last_make_outside_of_git: false
% 11.83/2.00  
% 11.83/2.00  ------ 
% 11.83/2.00  
% 11.83/2.00  ------ Input Options
% 11.83/2.00  
% 11.83/2.00  --out_options                           all
% 11.83/2.00  --tptp_safe_out                         true
% 11.83/2.00  --problem_path                          ""
% 11.83/2.00  --include_path                          ""
% 11.83/2.00  --clausifier                            res/vclausify_rel
% 11.83/2.00  --clausifier_options                    --mode clausify
% 11.83/2.00  --stdin                                 false
% 11.83/2.00  --stats_out                             sel
% 11.83/2.00  
% 11.83/2.00  ------ General Options
% 11.83/2.00  
% 11.83/2.00  --fof                                   false
% 11.83/2.00  --time_out_real                         604.99
% 11.83/2.00  --time_out_virtual                      -1.
% 11.83/2.00  --symbol_type_check                     false
% 11.83/2.00  --clausify_out                          false
% 11.83/2.00  --sig_cnt_out                           false
% 11.83/2.00  --trig_cnt_out                          false
% 11.83/2.00  --trig_cnt_out_tolerance                1.
% 11.83/2.00  --trig_cnt_out_sk_spl                   false
% 11.83/2.00  --abstr_cl_out                          false
% 11.83/2.00  
% 11.83/2.00  ------ Global Options
% 11.83/2.00  
% 11.83/2.00  --schedule                              none
% 11.83/2.00  --add_important_lit                     false
% 11.83/2.00  --prop_solver_per_cl                    1000
% 11.83/2.00  --min_unsat_core                        false
% 11.83/2.00  --soft_assumptions                      false
% 11.83/2.00  --soft_lemma_size                       3
% 11.83/2.00  --prop_impl_unit_size                   0
% 11.83/2.00  --prop_impl_unit                        []
% 11.83/2.00  --share_sel_clauses                     true
% 11.83/2.00  --reset_solvers                         false
% 11.83/2.00  --bc_imp_inh                            [conj_cone]
% 11.83/2.00  --conj_cone_tolerance                   3.
% 11.83/2.00  --extra_neg_conj                        none
% 11.83/2.00  --large_theory_mode                     true
% 11.83/2.00  --prolific_symb_bound                   200
% 11.83/2.00  --lt_threshold                          2000
% 11.83/2.00  --clause_weak_htbl                      true
% 11.83/2.00  --gc_record_bc_elim                     false
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing Options
% 11.83/2.00  
% 11.83/2.00  --preprocessing_flag                    true
% 11.83/2.00  --time_out_prep_mult                    0.1
% 11.83/2.00  --splitting_mode                        input
% 11.83/2.00  --splitting_grd                         true
% 11.83/2.00  --splitting_cvd                         false
% 11.83/2.00  --splitting_cvd_svl                     false
% 11.83/2.00  --splitting_nvd                         32
% 11.83/2.00  --sub_typing                            true
% 11.83/2.00  --prep_gs_sim                           false
% 11.83/2.00  --prep_unflatten                        true
% 11.83/2.00  --prep_res_sim                          true
% 11.83/2.00  --prep_upred                            true
% 11.83/2.00  --prep_sem_filter                       exhaustive
% 11.83/2.00  --prep_sem_filter_out                   false
% 11.83/2.00  --pred_elim                             false
% 11.83/2.00  --res_sim_input                         true
% 11.83/2.00  --eq_ax_congr_red                       true
% 11.83/2.00  --pure_diseq_elim                       true
% 11.83/2.00  --brand_transform                       false
% 11.83/2.00  --non_eq_to_eq                          false
% 11.83/2.00  --prep_def_merge                        true
% 11.83/2.00  --prep_def_merge_prop_impl              false
% 11.83/2.00  --prep_def_merge_mbd                    true
% 11.83/2.00  --prep_def_merge_tr_red                 false
% 11.83/2.00  --prep_def_merge_tr_cl                  false
% 11.83/2.00  --smt_preprocessing                     true
% 11.83/2.00  --smt_ac_axioms                         fast
% 11.83/2.00  --preprocessed_out                      false
% 11.83/2.00  --preprocessed_stats                    false
% 11.83/2.00  
% 11.83/2.00  ------ Abstraction refinement Options
% 11.83/2.00  
% 11.83/2.00  --abstr_ref                             []
% 11.83/2.00  --abstr_ref_prep                        false
% 11.83/2.00  --abstr_ref_until_sat                   false
% 11.83/2.00  --abstr_ref_sig_restrict                funpre
% 11.83/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.83/2.00  --abstr_ref_under                       []
% 11.83/2.00  
% 11.83/2.00  ------ SAT Options
% 11.83/2.00  
% 11.83/2.00  --sat_mode                              false
% 11.83/2.00  --sat_fm_restart_options                ""
% 11.83/2.00  --sat_gr_def                            false
% 11.83/2.00  --sat_epr_types                         true
% 11.83/2.00  --sat_non_cyclic_types                  false
% 11.83/2.00  --sat_finite_models                     false
% 11.83/2.00  --sat_fm_lemmas                         false
% 11.83/2.00  --sat_fm_prep                           false
% 11.83/2.00  --sat_fm_uc_incr                        true
% 11.83/2.00  --sat_out_model                         small
% 11.83/2.00  --sat_out_clauses                       false
% 11.83/2.00  
% 11.83/2.00  ------ QBF Options
% 11.83/2.00  
% 11.83/2.00  --qbf_mode                              false
% 11.83/2.00  --qbf_elim_univ                         false
% 11.83/2.00  --qbf_dom_inst                          none
% 11.83/2.00  --qbf_dom_pre_inst                      false
% 11.83/2.00  --qbf_sk_in                             false
% 11.83/2.00  --qbf_pred_elim                         true
% 11.83/2.00  --qbf_split                             512
% 11.83/2.00  
% 11.83/2.00  ------ BMC1 Options
% 11.83/2.00  
% 11.83/2.00  --bmc1_incremental                      false
% 11.83/2.00  --bmc1_axioms                           reachable_all
% 11.83/2.00  --bmc1_min_bound                        0
% 11.83/2.00  --bmc1_max_bound                        -1
% 11.83/2.00  --bmc1_max_bound_default                -1
% 11.83/2.00  --bmc1_symbol_reachability              true
% 11.83/2.00  --bmc1_property_lemmas                  false
% 11.83/2.00  --bmc1_k_induction                      false
% 11.83/2.00  --bmc1_non_equiv_states                 false
% 11.83/2.00  --bmc1_deadlock                         false
% 11.83/2.00  --bmc1_ucm                              false
% 11.83/2.00  --bmc1_add_unsat_core                   none
% 11.83/2.00  --bmc1_unsat_core_children              false
% 11.83/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.83/2.00  --bmc1_out_stat                         full
% 11.83/2.00  --bmc1_ground_init                      false
% 11.83/2.00  --bmc1_pre_inst_next_state              false
% 11.83/2.00  --bmc1_pre_inst_state                   false
% 11.83/2.00  --bmc1_pre_inst_reach_state             false
% 11.83/2.00  --bmc1_out_unsat_core                   false
% 11.83/2.00  --bmc1_aig_witness_out                  false
% 11.83/2.00  --bmc1_verbose                          false
% 11.83/2.00  --bmc1_dump_clauses_tptp                false
% 11.83/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.83/2.00  --bmc1_dump_file                        -
% 11.83/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.83/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.83/2.00  --bmc1_ucm_extend_mode                  1
% 11.83/2.00  --bmc1_ucm_init_mode                    2
% 11.83/2.00  --bmc1_ucm_cone_mode                    none
% 11.83/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.83/2.00  --bmc1_ucm_relax_model                  4
% 11.83/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.83/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.83/2.00  --bmc1_ucm_layered_model                none
% 11.83/2.00  --bmc1_ucm_max_lemma_size               10
% 11.83/2.00  
% 11.83/2.00  ------ AIG Options
% 11.83/2.00  
% 11.83/2.00  --aig_mode                              false
% 11.83/2.00  
% 11.83/2.00  ------ Instantiation Options
% 11.83/2.00  
% 11.83/2.00  --instantiation_flag                    true
% 11.83/2.00  --inst_sos_flag                         false
% 11.83/2.00  --inst_sos_phase                        true
% 11.83/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.83/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.83/2.00  --inst_lit_sel_side                     num_symb
% 11.83/2.00  --inst_solver_per_active                1400
% 11.83/2.00  --inst_solver_calls_frac                1.
% 11.83/2.00  --inst_passive_queue_type               priority_queues
% 11.83/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.83/2.00  --inst_passive_queues_freq              [25;2]
% 11.83/2.00  --inst_dismatching                      true
% 11.83/2.00  --inst_eager_unprocessed_to_passive     true
% 11.83/2.00  --inst_prop_sim_given                   true
% 11.83/2.00  --inst_prop_sim_new                     false
% 11.83/2.00  --inst_subs_new                         false
% 11.83/2.00  --inst_eq_res_simp                      false
% 11.83/2.00  --inst_subs_given                       false
% 11.83/2.00  --inst_orphan_elimination               true
% 11.83/2.00  --inst_learning_loop_flag               true
% 11.83/2.00  --inst_learning_start                   3000
% 11.83/2.00  --inst_learning_factor                  2
% 11.83/2.00  --inst_start_prop_sim_after_learn       3
% 11.83/2.00  --inst_sel_renew                        solver
% 11.83/2.00  --inst_lit_activity_flag                true
% 11.83/2.00  --inst_restr_to_given                   false
% 11.83/2.00  --inst_activity_threshold               500
% 11.83/2.00  --inst_out_proof                        true
% 11.83/2.00  
% 11.83/2.00  ------ Resolution Options
% 11.83/2.00  
% 11.83/2.00  --resolution_flag                       true
% 11.83/2.00  --res_lit_sel                           adaptive
% 11.83/2.00  --res_lit_sel_side                      none
% 11.83/2.00  --res_ordering                          kbo
% 11.83/2.00  --res_to_prop_solver                    active
% 11.83/2.00  --res_prop_simpl_new                    false
% 11.83/2.00  --res_prop_simpl_given                  true
% 11.83/2.00  --res_passive_queue_type                priority_queues
% 11.83/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.83/2.00  --res_passive_queues_freq               [15;5]
% 11.83/2.00  --res_forward_subs                      full
% 11.83/2.00  --res_backward_subs                     full
% 11.83/2.00  --res_forward_subs_resolution           true
% 11.83/2.00  --res_backward_subs_resolution          true
% 11.83/2.00  --res_orphan_elimination                true
% 11.83/2.00  --res_time_limit                        2.
% 11.83/2.00  --res_out_proof                         true
% 11.83/2.00  
% 11.83/2.00  ------ Superposition Options
% 11.83/2.00  
% 11.83/2.00  --superposition_flag                    true
% 11.83/2.00  --sup_passive_queue_type                priority_queues
% 11.83/2.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.83/2.00  --sup_passive_queues_freq               [1;4]
% 11.83/2.00  --demod_completeness_check              fast
% 11.83/2.00  --demod_use_ground                      true
% 11.83/2.00  --sup_to_prop_solver                    passive
% 11.83/2.00  --sup_prop_simpl_new                    true
% 11.83/2.00  --sup_prop_simpl_given                  true
% 11.83/2.00  --sup_fun_splitting                     false
% 11.83/2.00  --sup_smt_interval                      50000
% 11.83/2.00  
% 11.83/2.00  ------ Superposition Simplification Setup
% 11.83/2.00  
% 11.83/2.00  --sup_indices_passive                   []
% 11.83/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.83/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.83/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.83/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.83/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.83/2.00  --sup_full_bw                           [BwDemod]
% 11.83/2.00  --sup_immed_triv                        [TrivRules]
% 11.83/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.83/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.83/2.00  --sup_immed_bw_main                     []
% 11.83/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.83/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.83/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.83/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.83/2.00  
% 11.83/2.00  ------ Combination Options
% 11.83/2.00  
% 11.83/2.00  --comb_res_mult                         3
% 11.83/2.00  --comb_sup_mult                         2
% 11.83/2.00  --comb_inst_mult                        10
% 11.83/2.00  
% 11.83/2.00  ------ Debug Options
% 11.83/2.00  
% 11.83/2.00  --dbg_backtrace                         false
% 11.83/2.00  --dbg_dump_prop_clauses                 false
% 11.83/2.00  --dbg_dump_prop_clauses_file            -
% 11.83/2.00  --dbg_out_stat                          false
% 11.83/2.00  ------ Parsing...
% 11.83/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.83/2.00  ------ Proving...
% 11.83/2.00  ------ Problem Properties 
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  clauses                                 31
% 11.83/2.00  conjectures                             9
% 11.83/2.00  EPR                                     9
% 11.83/2.00  Horn                                    29
% 11.83/2.00  unary                                   10
% 11.83/2.00  binary                                  13
% 11.83/2.00  lits                                    67
% 11.83/2.00  lits eq                                 10
% 11.83/2.00  fd_pure                                 0
% 11.83/2.00  fd_pseudo                               0
% 11.83/2.00  fd_cond                                 1
% 11.83/2.00  fd_pseudo_cond                          1
% 11.83/2.00  AC symbols                              0
% 11.83/2.00  
% 11.83/2.00  ------ Input Options Time Limit: Unbounded
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  ------ 
% 11.83/2.00  Current options:
% 11.83/2.00  ------ 
% 11.83/2.00  
% 11.83/2.00  ------ Input Options
% 11.83/2.00  
% 11.83/2.00  --out_options                           all
% 11.83/2.00  --tptp_safe_out                         true
% 11.83/2.00  --problem_path                          ""
% 11.83/2.00  --include_path                          ""
% 11.83/2.00  --clausifier                            res/vclausify_rel
% 11.83/2.00  --clausifier_options                    --mode clausify
% 11.83/2.00  --stdin                                 false
% 11.83/2.00  --stats_out                             sel
% 11.83/2.00  
% 11.83/2.00  ------ General Options
% 11.83/2.00  
% 11.83/2.00  --fof                                   false
% 11.83/2.00  --time_out_real                         604.99
% 11.83/2.00  --time_out_virtual                      -1.
% 11.83/2.00  --symbol_type_check                     false
% 11.83/2.00  --clausify_out                          false
% 11.83/2.00  --sig_cnt_out                           false
% 11.83/2.00  --trig_cnt_out                          false
% 11.83/2.00  --trig_cnt_out_tolerance                1.
% 11.83/2.00  --trig_cnt_out_sk_spl                   false
% 11.83/2.00  --abstr_cl_out                          false
% 11.83/2.00  
% 11.83/2.00  ------ Global Options
% 11.83/2.00  
% 11.83/2.00  --schedule                              none
% 11.83/2.00  --add_important_lit                     false
% 11.83/2.00  --prop_solver_per_cl                    1000
% 11.83/2.00  --min_unsat_core                        false
% 11.83/2.00  --soft_assumptions                      false
% 11.83/2.00  --soft_lemma_size                       3
% 11.83/2.00  --prop_impl_unit_size                   0
% 11.83/2.00  --prop_impl_unit                        []
% 11.83/2.00  --share_sel_clauses                     true
% 11.83/2.00  --reset_solvers                         false
% 11.83/2.00  --bc_imp_inh                            [conj_cone]
% 11.83/2.00  --conj_cone_tolerance                   3.
% 11.83/2.00  --extra_neg_conj                        none
% 11.83/2.00  --large_theory_mode                     true
% 11.83/2.00  --prolific_symb_bound                   200
% 11.83/2.00  --lt_threshold                          2000
% 11.83/2.00  --clause_weak_htbl                      true
% 11.83/2.00  --gc_record_bc_elim                     false
% 11.83/2.00  
% 11.83/2.00  ------ Preprocessing Options
% 11.83/2.00  
% 11.83/2.00  --preprocessing_flag                    true
% 11.83/2.00  --time_out_prep_mult                    0.1
% 11.83/2.00  --splitting_mode                        input
% 11.83/2.00  --splitting_grd                         true
% 11.83/2.00  --splitting_cvd                         false
% 11.83/2.00  --splitting_cvd_svl                     false
% 11.83/2.00  --splitting_nvd                         32
% 11.83/2.00  --sub_typing                            true
% 11.83/2.00  --prep_gs_sim                           false
% 11.83/2.00  --prep_unflatten                        true
% 11.83/2.00  --prep_res_sim                          true
% 11.83/2.00  --prep_upred                            true
% 11.83/2.00  --prep_sem_filter                       exhaustive
% 11.83/2.00  --prep_sem_filter_out                   false
% 11.83/2.00  --pred_elim                             false
% 11.83/2.00  --res_sim_input                         true
% 11.83/2.00  --eq_ax_congr_red                       true
% 11.83/2.00  --pure_diseq_elim                       true
% 11.83/2.00  --brand_transform                       false
% 11.83/2.00  --non_eq_to_eq                          false
% 11.83/2.00  --prep_def_merge                        true
% 11.83/2.00  --prep_def_merge_prop_impl              false
% 11.83/2.00  --prep_def_merge_mbd                    true
% 11.83/2.00  --prep_def_merge_tr_red                 false
% 11.83/2.00  --prep_def_merge_tr_cl                  false
% 11.83/2.00  --smt_preprocessing                     true
% 11.83/2.00  --smt_ac_axioms                         fast
% 11.83/2.00  --preprocessed_out                      false
% 11.83/2.00  --preprocessed_stats                    false
% 11.83/2.00  
% 11.83/2.00  ------ Abstraction refinement Options
% 11.83/2.00  
% 11.83/2.00  --abstr_ref                             []
% 11.83/2.00  --abstr_ref_prep                        false
% 11.83/2.00  --abstr_ref_until_sat                   false
% 11.83/2.00  --abstr_ref_sig_restrict                funpre
% 11.83/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.83/2.00  --abstr_ref_under                       []
% 11.83/2.00  
% 11.83/2.00  ------ SAT Options
% 11.83/2.00  
% 11.83/2.00  --sat_mode                              false
% 11.83/2.00  --sat_fm_restart_options                ""
% 11.83/2.00  --sat_gr_def                            false
% 11.83/2.00  --sat_epr_types                         true
% 11.83/2.00  --sat_non_cyclic_types                  false
% 11.83/2.00  --sat_finite_models                     false
% 11.83/2.00  --sat_fm_lemmas                         false
% 11.83/2.00  --sat_fm_prep                           false
% 11.83/2.00  --sat_fm_uc_incr                        true
% 11.83/2.00  --sat_out_model                         small
% 11.83/2.00  --sat_out_clauses                       false
% 11.83/2.00  
% 11.83/2.00  ------ QBF Options
% 11.83/2.00  
% 11.83/2.00  --qbf_mode                              false
% 11.83/2.00  --qbf_elim_univ                         false
% 11.83/2.00  --qbf_dom_inst                          none
% 11.83/2.00  --qbf_dom_pre_inst                      false
% 11.83/2.00  --qbf_sk_in                             false
% 11.83/2.00  --qbf_pred_elim                         true
% 11.83/2.00  --qbf_split                             512
% 11.83/2.00  
% 11.83/2.00  ------ BMC1 Options
% 11.83/2.00  
% 11.83/2.00  --bmc1_incremental                      false
% 11.83/2.00  --bmc1_axioms                           reachable_all
% 11.83/2.00  --bmc1_min_bound                        0
% 11.83/2.00  --bmc1_max_bound                        -1
% 11.83/2.00  --bmc1_max_bound_default                -1
% 11.83/2.00  --bmc1_symbol_reachability              true
% 11.83/2.00  --bmc1_property_lemmas                  false
% 11.83/2.00  --bmc1_k_induction                      false
% 11.83/2.00  --bmc1_non_equiv_states                 false
% 11.83/2.00  --bmc1_deadlock                         false
% 11.83/2.00  --bmc1_ucm                              false
% 11.83/2.00  --bmc1_add_unsat_core                   none
% 11.83/2.00  --bmc1_unsat_core_children              false
% 11.83/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.83/2.00  --bmc1_out_stat                         full
% 11.83/2.00  --bmc1_ground_init                      false
% 11.83/2.00  --bmc1_pre_inst_next_state              false
% 11.83/2.00  --bmc1_pre_inst_state                   false
% 11.83/2.00  --bmc1_pre_inst_reach_state             false
% 11.83/2.00  --bmc1_out_unsat_core                   false
% 11.83/2.00  --bmc1_aig_witness_out                  false
% 11.83/2.00  --bmc1_verbose                          false
% 11.83/2.00  --bmc1_dump_clauses_tptp                false
% 11.83/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.83/2.00  --bmc1_dump_file                        -
% 11.83/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.83/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.83/2.00  --bmc1_ucm_extend_mode                  1
% 11.83/2.00  --bmc1_ucm_init_mode                    2
% 11.83/2.00  --bmc1_ucm_cone_mode                    none
% 11.83/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.83/2.00  --bmc1_ucm_relax_model                  4
% 11.83/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.83/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.83/2.00  --bmc1_ucm_layered_model                none
% 11.83/2.00  --bmc1_ucm_max_lemma_size               10
% 11.83/2.00  
% 11.83/2.00  ------ AIG Options
% 11.83/2.00  
% 11.83/2.00  --aig_mode                              false
% 11.83/2.00  
% 11.83/2.00  ------ Instantiation Options
% 11.83/2.00  
% 11.83/2.00  --instantiation_flag                    true
% 11.83/2.00  --inst_sos_flag                         false
% 11.83/2.00  --inst_sos_phase                        true
% 11.83/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.83/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.83/2.00  --inst_lit_sel_side                     num_symb
% 11.83/2.00  --inst_solver_per_active                1400
% 11.83/2.00  --inst_solver_calls_frac                1.
% 11.83/2.00  --inst_passive_queue_type               priority_queues
% 11.83/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.83/2.00  --inst_passive_queues_freq              [25;2]
% 11.83/2.00  --inst_dismatching                      true
% 11.83/2.00  --inst_eager_unprocessed_to_passive     true
% 11.83/2.00  --inst_prop_sim_given                   true
% 11.83/2.00  --inst_prop_sim_new                     false
% 11.83/2.00  --inst_subs_new                         false
% 11.83/2.00  --inst_eq_res_simp                      false
% 11.83/2.00  --inst_subs_given                       false
% 11.83/2.00  --inst_orphan_elimination               true
% 11.83/2.00  --inst_learning_loop_flag               true
% 11.83/2.00  --inst_learning_start                   3000
% 11.83/2.00  --inst_learning_factor                  2
% 11.83/2.00  --inst_start_prop_sim_after_learn       3
% 11.83/2.00  --inst_sel_renew                        solver
% 11.83/2.00  --inst_lit_activity_flag                true
% 11.83/2.00  --inst_restr_to_given                   false
% 11.83/2.00  --inst_activity_threshold               500
% 11.83/2.00  --inst_out_proof                        true
% 11.83/2.00  
% 11.83/2.00  ------ Resolution Options
% 11.83/2.00  
% 11.83/2.00  --resolution_flag                       true
% 11.83/2.00  --res_lit_sel                           adaptive
% 11.83/2.00  --res_lit_sel_side                      none
% 11.83/2.00  --res_ordering                          kbo
% 11.83/2.00  --res_to_prop_solver                    active
% 11.83/2.00  --res_prop_simpl_new                    false
% 11.83/2.00  --res_prop_simpl_given                  true
% 11.83/2.00  --res_passive_queue_type                priority_queues
% 11.83/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.83/2.00  --res_passive_queues_freq               [15;5]
% 11.83/2.00  --res_forward_subs                      full
% 11.83/2.00  --res_backward_subs                     full
% 11.83/2.00  --res_forward_subs_resolution           true
% 11.83/2.00  --res_backward_subs_resolution          true
% 11.83/2.00  --res_orphan_elimination                true
% 11.83/2.00  --res_time_limit                        2.
% 11.83/2.00  --res_out_proof                         true
% 11.83/2.00  
% 11.83/2.00  ------ Superposition Options
% 11.83/2.00  
% 11.83/2.00  --superposition_flag                    true
% 11.83/2.00  --sup_passive_queue_type                priority_queues
% 11.83/2.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.83/2.00  --sup_passive_queues_freq               [1;4]
% 11.83/2.00  --demod_completeness_check              fast
% 11.83/2.00  --demod_use_ground                      true
% 11.83/2.00  --sup_to_prop_solver                    passive
% 11.83/2.00  --sup_prop_simpl_new                    true
% 11.83/2.00  --sup_prop_simpl_given                  true
% 11.83/2.00  --sup_fun_splitting                     false
% 11.83/2.00  --sup_smt_interval                      50000
% 11.83/2.00  
% 11.83/2.00  ------ Superposition Simplification Setup
% 11.83/2.00  
% 11.83/2.00  --sup_indices_passive                   []
% 11.83/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.83/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.83/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.83/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.83/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.83/2.00  --sup_full_bw                           [BwDemod]
% 11.83/2.00  --sup_immed_triv                        [TrivRules]
% 11.83/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.83/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.83/2.00  --sup_immed_bw_main                     []
% 11.83/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.83/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.83/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.83/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.83/2.00  
% 11.83/2.00  ------ Combination Options
% 11.83/2.00  
% 11.83/2.00  --comb_res_mult                         3
% 11.83/2.00  --comb_sup_mult                         2
% 11.83/2.00  --comb_inst_mult                        10
% 11.83/2.00  
% 11.83/2.00  ------ Debug Options
% 11.83/2.00  
% 11.83/2.00  --dbg_backtrace                         false
% 11.83/2.00  --dbg_dump_prop_clauses                 false
% 11.83/2.00  --dbg_dump_prop_clauses_file            -
% 11.83/2.00  --dbg_out_stat                          false
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  ------ Proving...
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  % SZS status Theorem for theBenchmark.p
% 11.83/2.00  
% 11.83/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.83/2.00  
% 11.83/2.00  fof(f18,conjecture,(
% 11.83/2.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f19,negated_conjecture,(
% 11.83/2.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 11.83/2.00    inference(negated_conjecture,[],[f18])).
% 11.83/2.00  
% 11.83/2.00  fof(f38,plain,(
% 11.83/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 11.83/2.00    inference(ennf_transformation,[],[f19])).
% 11.83/2.00  
% 11.83/2.00  fof(f39,plain,(
% 11.83/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 11.83/2.00    inference(flattening,[],[f38])).
% 11.83/2.00  
% 11.83/2.00  fof(f43,plain,(
% 11.83/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 11.83/2.00    inference(nnf_transformation,[],[f39])).
% 11.83/2.00  
% 11.83/2.00  fof(f44,plain,(
% 11.83/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 11.83/2.00    inference(flattening,[],[f43])).
% 11.83/2.00  
% 11.83/2.00  fof(f49,plain,(
% 11.83/2.00    ( ! [X2,X0,X3,X1] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) => ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,sK4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),sK4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,sK4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(X1)))) )),
% 11.83/2.00    introduced(choice_axiom,[])).
% 11.83/2.00  
% 11.83/2.00  fof(f48,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : ((~r1_tarski(sK3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,sK3),X4)) & (r1_tarski(sK3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,sK3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 11.83/2.00    introduced(choice_axiom,[])).
% 11.83/2.00  
% 11.83/2.00  fof(f47,plain,(
% 11.83/2.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,sK2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,sK2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,sK2,X4)) | r1_tarski(k7_relset_1(X0,X1,sK2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK2,X0,X1) & v1_funct_1(sK2))) )),
% 11.83/2.00    introduced(choice_axiom,[])).
% 11.83/2.00  
% 11.83/2.00  fof(f46,plain,(
% 11.83/2.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,sK1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,sK1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,sK1,X2,X4)) | r1_tarski(k7_relset_1(X0,sK1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) & v1_funct_2(X2,X0,sK1) & v1_funct_1(X2)) & ~v1_xboole_0(sK1))) )),
% 11.83/2.00    introduced(choice_axiom,[])).
% 11.83/2.00  
% 11.83/2.00  fof(f45,plain,(
% 11.83/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 11.83/2.00    introduced(choice_axiom,[])).
% 11.83/2.00  
% 11.83/2.00  fof(f50,plain,(
% 11.83/2.00    (((((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 11.83/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f44,f49,f48,f47,f46,f45])).
% 11.83/2.00  
% 11.83/2.00  fof(f78,plain,(
% 11.83/2.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.83/2.00    inference(cnf_transformation,[],[f50])).
% 11.83/2.00  
% 11.83/2.00  fof(f14,axiom,(
% 11.83/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f33,plain,(
% 11.83/2.00    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.83/2.00    inference(ennf_transformation,[],[f14])).
% 11.83/2.00  
% 11.83/2.00  fof(f67,plain,(
% 11.83/2.00    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f33])).
% 11.83/2.00  
% 11.83/2.00  fof(f17,axiom,(
% 11.83/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f36,plain,(
% 11.83/2.00    ! [X0,X1,X2,X3] : (((r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 11.83/2.00    inference(ennf_transformation,[],[f17])).
% 11.83/2.00  
% 11.83/2.00  fof(f37,plain,(
% 11.83/2.00    ! [X0,X1,X2,X3] : (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 11.83/2.00    inference(flattening,[],[f36])).
% 11.83/2.00  
% 11.83/2.00  fof(f72,plain,(
% 11.83/2.00    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | k1_xboole_0 = X1 | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f37])).
% 11.83/2.00  
% 11.83/2.00  fof(f75,plain,(
% 11.83/2.00    ~v1_xboole_0(sK1)),
% 11.83/2.00    inference(cnf_transformation,[],[f50])).
% 11.83/2.00  
% 11.83/2.00  fof(f76,plain,(
% 11.83/2.00    v1_funct_1(sK2)),
% 11.83/2.00    inference(cnf_transformation,[],[f50])).
% 11.83/2.00  
% 11.83/2.00  fof(f77,plain,(
% 11.83/2.00    v1_funct_2(sK2,sK0,sK1)),
% 11.83/2.00    inference(cnf_transformation,[],[f50])).
% 11.83/2.00  
% 11.83/2.00  fof(f1,axiom,(
% 11.83/2.00    v1_xboole_0(k1_xboole_0)),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f51,plain,(
% 11.83/2.00    v1_xboole_0(k1_xboole_0)),
% 11.83/2.00    inference(cnf_transformation,[],[f1])).
% 11.83/2.00  
% 11.83/2.00  fof(f13,axiom,(
% 11.83/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f32,plain,(
% 11.83/2.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.83/2.00    inference(ennf_transformation,[],[f13])).
% 11.83/2.00  
% 11.83/2.00  fof(f66,plain,(
% 11.83/2.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f32])).
% 11.83/2.00  
% 11.83/2.00  fof(f79,plain,(
% 11.83/2.00    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 11.83/2.00    inference(cnf_transformation,[],[f50])).
% 11.83/2.00  
% 11.83/2.00  fof(f6,axiom,(
% 11.83/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f42,plain,(
% 11.83/2.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.83/2.00    inference(nnf_transformation,[],[f6])).
% 11.83/2.00  
% 11.83/2.00  fof(f58,plain,(
% 11.83/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f42])).
% 11.83/2.00  
% 11.83/2.00  fof(f5,axiom,(
% 11.83/2.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f22,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.83/2.00    inference(ennf_transformation,[],[f5])).
% 11.83/2.00  
% 11.83/2.00  fof(f23,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.83/2.00    inference(flattening,[],[f22])).
% 11.83/2.00  
% 11.83/2.00  fof(f57,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f23])).
% 11.83/2.00  
% 11.83/2.00  fof(f16,axiom,(
% 11.83/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f35,plain,(
% 11.83/2.00    ! [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 11.83/2.00    inference(ennf_transformation,[],[f16])).
% 11.83/2.00  
% 11.83/2.00  fof(f71,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f35])).
% 11.83/2.00  
% 11.83/2.00  fof(f12,axiom,(
% 11.83/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f31,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.83/2.00    inference(ennf_transformation,[],[f12])).
% 11.83/2.00  
% 11.83/2.00  fof(f65,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f31])).
% 11.83/2.00  
% 11.83/2.00  fof(f81,plain,(
% 11.83/2.00    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 11.83/2.00    inference(cnf_transformation,[],[f50])).
% 11.83/2.00  
% 11.83/2.00  fof(f11,axiom,(
% 11.83/2.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f29,plain,(
% 11.83/2.00    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 11.83/2.00    inference(ennf_transformation,[],[f11])).
% 11.83/2.00  
% 11.83/2.00  fof(f30,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.83/2.00    inference(flattening,[],[f29])).
% 11.83/2.00  
% 11.83/2.00  fof(f64,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f30])).
% 11.83/2.00  
% 11.83/2.00  fof(f7,axiom,(
% 11.83/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f24,plain,(
% 11.83/2.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.83/2.00    inference(ennf_transformation,[],[f7])).
% 11.83/2.00  
% 11.83/2.00  fof(f60,plain,(
% 11.83/2.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f24])).
% 11.83/2.00  
% 11.83/2.00  fof(f59,plain,(
% 11.83/2.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f42])).
% 11.83/2.00  
% 11.83/2.00  fof(f8,axiom,(
% 11.83/2.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f61,plain,(
% 11.83/2.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.83/2.00    inference(cnf_transformation,[],[f8])).
% 11.83/2.00  
% 11.83/2.00  fof(f10,axiom,(
% 11.83/2.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f27,plain,(
% 11.83/2.00    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.83/2.00    inference(ennf_transformation,[],[f10])).
% 11.83/2.00  
% 11.83/2.00  fof(f28,plain,(
% 11.83/2.00    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.83/2.00    inference(flattening,[],[f27])).
% 11.83/2.00  
% 11.83/2.00  fof(f63,plain,(
% 11.83/2.00    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f28])).
% 11.83/2.00  
% 11.83/2.00  fof(f9,axiom,(
% 11.83/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f25,plain,(
% 11.83/2.00    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 11.83/2.00    inference(ennf_transformation,[],[f9])).
% 11.83/2.00  
% 11.83/2.00  fof(f26,plain,(
% 11.83/2.00    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 11.83/2.00    inference(flattening,[],[f25])).
% 11.83/2.00  
% 11.83/2.00  fof(f62,plain,(
% 11.83/2.00    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 11.83/2.00    inference(cnf_transformation,[],[f26])).
% 11.83/2.00  
% 11.83/2.00  fof(f82,plain,(
% 11.83/2.00    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 11.83/2.00    inference(cnf_transformation,[],[f50])).
% 11.83/2.00  
% 11.83/2.00  fof(f2,axiom,(
% 11.83/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.83/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.83/2.00  
% 11.83/2.00  fof(f40,plain,(
% 11.83/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.83/2.00    inference(nnf_transformation,[],[f2])).
% 11.83/2.00  
% 11.83/2.00  fof(f41,plain,(
% 11.83/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.83/2.00    inference(flattening,[],[f40])).
% 11.83/2.00  
% 11.83/2.00  fof(f52,plain,(
% 11.83/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.83/2.00    inference(cnf_transformation,[],[f41])).
% 11.83/2.00  
% 11.83/2.00  fof(f84,plain,(
% 11.83/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.83/2.00    inference(equality_resolution,[],[f52])).
% 11.83/2.00  
% 11.83/2.00  cnf(c_27,negated_conjecture,
% 11.83/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.83/2.00      inference(cnf_transformation,[],[f78]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1276,plain,
% 11.83/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_16,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.83/2.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 11.83/2.00      inference(cnf_transformation,[],[f67]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1287,plain,
% 11.83/2.00      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 11.83/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2528,plain,
% 11.83/2.00      ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_1276,c_1287]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_22,plain,
% 11.83/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.83/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.83/2.00      | ~ r1_tarski(X3,X1)
% 11.83/2.00      | r1_tarski(X3,k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X3)))
% 11.83/2.00      | ~ v1_funct_1(X0)
% 11.83/2.00      | k1_xboole_0 = X2 ),
% 11.83/2.00      inference(cnf_transformation,[],[f72]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1281,plain,
% 11.83/2.00      ( k1_xboole_0 = X0
% 11.83/2.00      | v1_funct_2(X1,X2,X0) != iProver_top
% 11.83/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 11.83/2.00      | r1_tarski(X3,X2) != iProver_top
% 11.83/2.00      | r1_tarski(X3,k8_relset_1(X2,X0,X1,k7_relset_1(X2,X0,X1,X3))) = iProver_top
% 11.83/2.00      | v1_funct_1(X1) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4778,plain,
% 11.83/2.00      ( sK1 = k1_xboole_0
% 11.83/2.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.83/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.83/2.00      | r1_tarski(X0,k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,X0))) = iProver_top
% 11.83/2.00      | r1_tarski(X0,sK0) != iProver_top
% 11.83/2.00      | v1_funct_1(sK2) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_2528,c_1281]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_30,negated_conjecture,
% 11.83/2.00      ( ~ v1_xboole_0(sK1) ),
% 11.83/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_29,negated_conjecture,
% 11.83/2.00      ( v1_funct_1(sK2) ),
% 11.83/2.00      inference(cnf_transformation,[],[f76]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_34,plain,
% 11.83/2.00      ( v1_funct_1(sK2) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_28,negated_conjecture,
% 11.83/2.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 11.83/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_35,plain,
% 11.83/2.00      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_36,plain,
% 11.83/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_0,plain,
% 11.83/2.00      ( v1_xboole_0(k1_xboole_0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_567,plain,
% 11.83/2.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 11.83/2.00      theory(equality) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1542,plain,
% 11.83/2.00      ( v1_xboole_0(X0)
% 11.83/2.00      | ~ v1_xboole_0(k1_xboole_0)
% 11.83/2.00      | X0 != k1_xboole_0 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_567]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_38529,plain,
% 11.83/2.00      ( v1_xboole_0(sK1)
% 11.83/2.00      | ~ v1_xboole_0(k1_xboole_0)
% 11.83/2.00      | sK1 != k1_xboole_0 ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_1542]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_42245,plain,
% 11.83/2.00      ( r1_tarski(X0,sK0) != iProver_top
% 11.83/2.00      | r1_tarski(X0,k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,X0))) = iProver_top ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_4778,c_30,c_34,c_35,c_36,c_0,c_38529]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_42246,plain,
% 11.83/2.00      ( r1_tarski(X0,k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,X0))) = iProver_top
% 11.83/2.00      | r1_tarski(X0,sK0) != iProver_top ),
% 11.83/2.00      inference(renaming,[status(thm)],[c_42245]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_15,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.83/2.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 11.83/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1288,plain,
% 11.83/2.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 11.83/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2543,plain,
% 11.83/2.00      ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_1276,c_1288]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_42251,plain,
% 11.83/2.00      ( r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) = iProver_top
% 11.83/2.00      | r1_tarski(X0,sK0) != iProver_top ),
% 11.83/2.00      inference(light_normalisation,[status(thm)],[c_42246,c_2543]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_26,negated_conjecture,
% 11.83/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 11.83/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1277,plain,
% 11.83/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_8,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.83/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1294,plain,
% 11.83/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.83/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1949,plain,
% 11.83/2.00      ( r1_tarski(sK3,sK0) = iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_1277,c_1294]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_6,plain,
% 11.83/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 11.83/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1296,plain,
% 11.83/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.83/2.00      | r1_tarski(X1,X2) != iProver_top
% 11.83/2.00      | r1_tarski(X0,X2) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4063,plain,
% 11.83/2.00      ( r1_tarski(sK0,X0) != iProver_top
% 11.83/2.00      | r1_tarski(sK3,X0) = iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_1949,c_1296]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_42288,plain,
% 11.83/2.00      ( r1_tarski(sK0,sK0) != iProver_top
% 11.83/2.00      | r1_tarski(sK3,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) = iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_42251,c_4063]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_19,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.83/2.00      | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = k1_relset_1(X1,X2,X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1284,plain,
% 11.83/2.00      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = k1_relset_1(X0,X1,X2)
% 11.83/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3545,plain,
% 11.83/2.00      ( k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) = k1_relset_1(sK0,sK1,sK2) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_1276,c_1284]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_14,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.83/2.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1289,plain,
% 11.83/2.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.83/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2364,plain,
% 11.83/2.00      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_1276,c_1289]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_6939,plain,
% 11.83/2.00      ( k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) = k1_relat_1(sK2) ),
% 11.83/2.00      inference(light_normalisation,[status(thm)],[c_3545,c_2364]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_6940,plain,
% 11.83/2.00      ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = k1_relat_1(sK2) ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_6939,c_2528,c_2543]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_42371,plain,
% 11.83/2.00      ( r1_tarski(sK0,sK0) != iProver_top
% 11.83/2.00      | r1_tarski(sK3,k1_relat_1(sK2)) = iProver_top ),
% 11.83/2.00      inference(light_normalisation,[status(thm)],[c_42288,c_6940]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_24,negated_conjecture,
% 11.83/2.00      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
% 11.83/2.00      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
% 11.83/2.00      inference(cnf_transformation,[],[f81]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1279,plain,
% 11.83/2.00      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
% 11.83/2.00      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4767,plain,
% 11.83/2.00      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
% 11.83/2.00      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_2528,c_1279]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_8050,plain,
% 11.83/2.00      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
% 11.83/2.00      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_4767,c_2543]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_13,plain,
% 11.83/2.00      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 11.83/2.00      | ~ r1_tarski(X0,k1_relat_1(X1))
% 11.83/2.00      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 11.83/2.00      | ~ v1_funct_1(X1)
% 11.83/2.00      | ~ v1_relat_1(X1) ),
% 11.83/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1290,plain,
% 11.83/2.00      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 11.83/2.00      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 11.83/2.00      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 11.83/2.00      | v1_funct_1(X1) != iProver_top
% 11.83/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_8058,plain,
% 11.83/2.00      ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top
% 11.83/2.00      | r1_tarski(sK3,k1_relat_1(sK2)) != iProver_top
% 11.83/2.00      | v1_funct_1(sK2) != iProver_top
% 11.83/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_8050,c_1290]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9,plain,
% 11.83/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.83/2.00      | ~ v1_relat_1(X1)
% 11.83/2.00      | v1_relat_1(X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_7,plain,
% 11.83/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.83/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_212,plain,
% 11.83/2.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.83/2.00      inference(prop_impl,[status(thm)],[c_7]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_213,plain,
% 11.83/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.83/2.00      inference(renaming,[status(thm)],[c_212]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_271,plain,
% 11.83/2.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 11.83/2.00      inference(bin_hyper_res,[status(thm)],[c_9,c_213]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1719,plain,
% 11.83/2.00      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
% 11.83/2.00      inference(resolution,[status(thm)],[c_8,c_27]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2146,plain,
% 11.83/2.00      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2) ),
% 11.83/2.00      inference(resolution,[status(thm)],[c_271,c_1719]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_10,plain,
% 11.83/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.83/2.00      inference(cnf_transformation,[],[f61]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2402,plain,
% 11.83/2.00      ( v1_relat_1(sK2) ),
% 11.83/2.00      inference(forward_subsumption_resolution,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_2146,c_10]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_2403,plain,
% 11.83/2.00      ( v1_relat_1(sK2) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_2402]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_16588,plain,
% 11.83/2.00      ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top
% 11.83/2.00      | r1_tarski(sK3,k1_relat_1(sK2)) != iProver_top ),
% 11.83/2.00      inference(global_propositional_subsumption,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_8058,c_34,c_2403]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_12,plain,
% 11.83/2.00      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 11.83/2.00      | ~ v1_funct_1(X0)
% 11.83/2.00      | ~ v1_relat_1(X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1291,plain,
% 11.83/2.00      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 11.83/2.00      | v1_funct_1(X0) != iProver_top
% 11.83/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_11,plain,
% 11.83/2.00      ( ~ r1_tarski(X0,X1)
% 11.83/2.00      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 11.83/2.00      | ~ v1_relat_1(X2) ),
% 11.83/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1292,plain,
% 11.83/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.83/2.00      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
% 11.83/2.00      | v1_relat_1(X2) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3366,plain,
% 11.83/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.83/2.00      | r1_tarski(k9_relat_1(X2,X1),X3) != iProver_top
% 11.83/2.00      | r1_tarski(k9_relat_1(X2,X0),X3) = iProver_top
% 11.83/2.00      | v1_relat_1(X2) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_1292,c_1296]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_18051,plain,
% 11.83/2.00      ( r1_tarski(X0,k10_relat_1(X1,X2)) != iProver_top
% 11.83/2.00      | r1_tarski(k9_relat_1(X1,X0),X2) = iProver_top
% 11.83/2.00      | v1_funct_1(X1) != iProver_top
% 11.83/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_1291,c_3366]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_18703,plain,
% 11.83/2.00      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
% 11.83/2.00      | r1_tarski(sK3,k1_relat_1(sK2)) != iProver_top
% 11.83/2.00      | v1_funct_1(sK2) != iProver_top
% 11.83/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_16588,c_18051]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_23,negated_conjecture,
% 11.83/2.00      ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
% 11.83/2.00      | ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
% 11.83/2.00      inference(cnf_transformation,[],[f82]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_1280,plain,
% 11.83/2.00      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
% 11.83/2.00      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) != iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_4766,plain,
% 11.83/2.00      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
% 11.83/2.00      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_2528,c_1280]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_9375,plain,
% 11.83/2.00      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top
% 11.83/2.00      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
% 11.83/2.00      inference(demodulation,[status(thm)],[c_4766,c_2543]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_16601,plain,
% 11.83/2.00      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top
% 11.83/2.00      | r1_tarski(sK3,k1_relat_1(sK2)) != iProver_top ),
% 11.83/2.00      inference(superposition,[status(thm)],[c_16588,c_9375]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_3,plain,
% 11.83/2.00      ( r1_tarski(X0,X0) ),
% 11.83/2.00      inference(cnf_transformation,[],[f84]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_94,plain,
% 11.83/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 11.83/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(c_96,plain,
% 11.83/2.00      ( r1_tarski(sK0,sK0) = iProver_top ),
% 11.83/2.00      inference(instantiation,[status(thm)],[c_94]) ).
% 11.83/2.00  
% 11.83/2.00  cnf(contradiction,plain,
% 11.83/2.00      ( $false ),
% 11.83/2.00      inference(minisat,
% 11.83/2.00                [status(thm)],
% 11.83/2.00                [c_42371,c_18703,c_16601,c_2403,c_96,c_34]) ).
% 11.83/2.00  
% 11.83/2.00  
% 11.83/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.83/2.00  
% 11.83/2.00  ------                               Statistics
% 11.83/2.00  
% 11.83/2.00  ------ Selected
% 11.83/2.00  
% 11.83/2.00  total_time:                             1.231
% 11.83/2.00  
%------------------------------------------------------------------------------

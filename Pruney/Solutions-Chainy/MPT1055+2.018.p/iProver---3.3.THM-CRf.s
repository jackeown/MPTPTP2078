%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:10 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 733 expanded)
%              Number of clauses        :   83 ( 214 expanded)
%              Number of leaves         :   19 ( 222 expanded)
%              Depth                    :   23
%              Number of atoms          :  475 (5377 expanded)
%              Number of equality atoms :  144 ( 294 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f35,f40,f39,f38,f37,f36])).

fof(f63,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f62,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_8,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_383,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_384,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_1834,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_384])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_32,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_385,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_384])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1974,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1975,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1974])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_213,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_214,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_213])).

cnf(c_271,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_214])).

cnf(c_1977,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_2295,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1977])).

cnf(c_2296,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2295])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2344,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2345,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2344])).

cnf(c_2386,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1834,c_32,c_385,c_1975,c_2296,c_2345])).

cnf(c_1836,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1846,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2172,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1836,c_1846])).

cnf(c_1835,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_271])).

cnf(c_2562,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2172,c_1835])).

cnf(c_3634,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2562,c_32,c_1975,c_2296,c_2345])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1841,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2708,plain,
    ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1836,c_1841])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1839,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1848,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2165,plain,
    ( k2_xboole_0(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = sK4
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1839,c_1848])).

cnf(c_2863,plain,
    ( k2_xboole_0(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = sK4
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2708,c_2165])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1971,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | r1_tarski(sK3,sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1972,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1971])).

cnf(c_2864,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2708,c_1839])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1842,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2803,plain,
    ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1836,c_1842])).

cnf(c_3026,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2864,c_2803])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_453,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_454,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_456,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_454,c_23])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1843,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2694,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1836,c_1843])).

cnf(c_2815,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_456,c_2694])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_373,plain,
    ( sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_26])).

cnf(c_2932,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2815,c_373])).

cnf(c_9,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_395,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_396,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,X1))
    | ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_1833,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_2936,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2932,c_1833])).

cnf(c_3779,plain,
    ( r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2936,c_32,c_1975,c_2296,c_2345])).

cnf(c_3780,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3779])).

cnf(c_3790,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top
    | r1_tarski(sK3,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3026,c_3780])).

cnf(c_3825,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2863,c_33,c_1972,c_3790])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1844,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3168,plain,
    ( k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,X2)
    | r1_tarski(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1844,c_1848])).

cnf(c_7133,plain,
    ( k2_xboole_0(k9_relat_1(X0,sK3),k9_relat_1(X0,k10_relat_1(sK2,sK4))) = k9_relat_1(X0,k10_relat_1(sK2,sK4))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3825,c_3168])).

cnf(c_9452,plain,
    ( k2_xboole_0(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) = k9_relat_1(sK2,k10_relat_1(sK2,sK4)) ),
    inference(superposition,[status(thm)],[c_3634,c_7133])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1849,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9610,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK4)),X0) != iProver_top
    | r1_tarski(k9_relat_1(sK2,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9452,c_1849])).

cnf(c_9790,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2386,c_9610])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1840,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2865,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2708,c_1840])).

cnf(c_2928,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2865,c_2803])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9790,c_3790,c_2928,c_1972,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:35:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.53/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.53/0.99  
% 3.53/0.99  ------  iProver source info
% 3.53/0.99  
% 3.53/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.53/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.53/0.99  git: non_committed_changes: false
% 3.53/0.99  git: last_make_outside_of_git: false
% 3.53/0.99  
% 3.53/0.99  ------ 
% 3.53/0.99  
% 3.53/0.99  ------ Input Options
% 3.53/0.99  
% 3.53/0.99  --out_options                           all
% 3.53/0.99  --tptp_safe_out                         true
% 3.53/0.99  --problem_path                          ""
% 3.53/0.99  --include_path                          ""
% 3.53/0.99  --clausifier                            res/vclausify_rel
% 3.53/0.99  --clausifier_options                    --mode clausify
% 3.53/0.99  --stdin                                 false
% 3.53/0.99  --stats_out                             all
% 3.53/0.99  
% 3.53/0.99  ------ General Options
% 3.53/0.99  
% 3.53/0.99  --fof                                   false
% 3.53/0.99  --time_out_real                         305.
% 3.53/0.99  --time_out_virtual                      -1.
% 3.53/0.99  --symbol_type_check                     false
% 3.53/0.99  --clausify_out                          false
% 3.53/0.99  --sig_cnt_out                           false
% 3.53/0.99  --trig_cnt_out                          false
% 3.53/0.99  --trig_cnt_out_tolerance                1.
% 3.53/0.99  --trig_cnt_out_sk_spl                   false
% 3.53/0.99  --abstr_cl_out                          false
% 3.53/0.99  
% 3.53/0.99  ------ Global Options
% 3.53/0.99  
% 3.53/0.99  --schedule                              default
% 3.53/0.99  --add_important_lit                     false
% 3.53/0.99  --prop_solver_per_cl                    1000
% 3.53/0.99  --min_unsat_core                        false
% 3.53/0.99  --soft_assumptions                      false
% 3.53/0.99  --soft_lemma_size                       3
% 3.53/0.99  --prop_impl_unit_size                   0
% 3.53/0.99  --prop_impl_unit                        []
% 3.53/0.99  --share_sel_clauses                     true
% 3.53/0.99  --reset_solvers                         false
% 3.53/0.99  --bc_imp_inh                            [conj_cone]
% 3.53/0.99  --conj_cone_tolerance                   3.
% 3.53/0.99  --extra_neg_conj                        none
% 3.53/0.99  --large_theory_mode                     true
% 3.53/0.99  --prolific_symb_bound                   200
% 3.53/0.99  --lt_threshold                          2000
% 3.53/0.99  --clause_weak_htbl                      true
% 3.53/0.99  --gc_record_bc_elim                     false
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing Options
% 3.53/0.99  
% 3.53/0.99  --preprocessing_flag                    true
% 3.53/0.99  --time_out_prep_mult                    0.1
% 3.53/0.99  --splitting_mode                        input
% 3.53/0.99  --splitting_grd                         true
% 3.53/0.99  --splitting_cvd                         false
% 3.53/0.99  --splitting_cvd_svl                     false
% 3.53/0.99  --splitting_nvd                         32
% 3.53/0.99  --sub_typing                            true
% 3.53/0.99  --prep_gs_sim                           true
% 3.53/0.99  --prep_unflatten                        true
% 3.53/0.99  --prep_res_sim                          true
% 3.53/0.99  --prep_upred                            true
% 3.53/0.99  --prep_sem_filter                       exhaustive
% 3.53/0.99  --prep_sem_filter_out                   false
% 3.53/0.99  --pred_elim                             true
% 3.53/0.99  --res_sim_input                         true
% 3.53/0.99  --eq_ax_congr_red                       true
% 3.53/0.99  --pure_diseq_elim                       true
% 3.53/0.99  --brand_transform                       false
% 3.53/0.99  --non_eq_to_eq                          false
% 3.53/0.99  --prep_def_merge                        true
% 3.53/0.99  --prep_def_merge_prop_impl              false
% 3.53/0.99  --prep_def_merge_mbd                    true
% 3.53/0.99  --prep_def_merge_tr_red                 false
% 3.53/0.99  --prep_def_merge_tr_cl                  false
% 3.53/0.99  --smt_preprocessing                     true
% 3.53/0.99  --smt_ac_axioms                         fast
% 3.53/0.99  --preprocessed_out                      false
% 3.53/0.99  --preprocessed_stats                    false
% 3.53/0.99  
% 3.53/0.99  ------ Abstraction refinement Options
% 3.53/0.99  
% 3.53/0.99  --abstr_ref                             []
% 3.53/0.99  --abstr_ref_prep                        false
% 3.53/0.99  --abstr_ref_until_sat                   false
% 3.53/0.99  --abstr_ref_sig_restrict                funpre
% 3.53/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/0.99  --abstr_ref_under                       []
% 3.53/0.99  
% 3.53/0.99  ------ SAT Options
% 3.53/0.99  
% 3.53/0.99  --sat_mode                              false
% 3.53/0.99  --sat_fm_restart_options                ""
% 3.53/0.99  --sat_gr_def                            false
% 3.53/0.99  --sat_epr_types                         true
% 3.53/0.99  --sat_non_cyclic_types                  false
% 3.53/0.99  --sat_finite_models                     false
% 3.53/0.99  --sat_fm_lemmas                         false
% 3.53/0.99  --sat_fm_prep                           false
% 3.53/0.99  --sat_fm_uc_incr                        true
% 3.53/0.99  --sat_out_model                         small
% 3.53/0.99  --sat_out_clauses                       false
% 3.53/0.99  
% 3.53/0.99  ------ QBF Options
% 3.53/0.99  
% 3.53/0.99  --qbf_mode                              false
% 3.53/0.99  --qbf_elim_univ                         false
% 3.53/0.99  --qbf_dom_inst                          none
% 3.53/0.99  --qbf_dom_pre_inst                      false
% 3.53/0.99  --qbf_sk_in                             false
% 3.53/0.99  --qbf_pred_elim                         true
% 3.53/0.99  --qbf_split                             512
% 3.53/0.99  
% 3.53/0.99  ------ BMC1 Options
% 3.53/0.99  
% 3.53/0.99  --bmc1_incremental                      false
% 3.53/0.99  --bmc1_axioms                           reachable_all
% 3.53/0.99  --bmc1_min_bound                        0
% 3.53/0.99  --bmc1_max_bound                        -1
% 3.53/0.99  --bmc1_max_bound_default                -1
% 3.53/0.99  --bmc1_symbol_reachability              true
% 3.53/0.99  --bmc1_property_lemmas                  false
% 3.53/0.99  --bmc1_k_induction                      false
% 3.53/0.99  --bmc1_non_equiv_states                 false
% 3.53/0.99  --bmc1_deadlock                         false
% 3.53/0.99  --bmc1_ucm                              false
% 3.53/0.99  --bmc1_add_unsat_core                   none
% 3.53/0.99  --bmc1_unsat_core_children              false
% 3.53/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/0.99  --bmc1_out_stat                         full
% 3.53/0.99  --bmc1_ground_init                      false
% 3.53/0.99  --bmc1_pre_inst_next_state              false
% 3.53/0.99  --bmc1_pre_inst_state                   false
% 3.53/0.99  --bmc1_pre_inst_reach_state             false
% 3.53/0.99  --bmc1_out_unsat_core                   false
% 3.53/0.99  --bmc1_aig_witness_out                  false
% 3.53/0.99  --bmc1_verbose                          false
% 3.53/0.99  --bmc1_dump_clauses_tptp                false
% 3.53/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.53/0.99  --bmc1_dump_file                        -
% 3.53/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.53/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.53/0.99  --bmc1_ucm_extend_mode                  1
% 3.53/0.99  --bmc1_ucm_init_mode                    2
% 3.53/0.99  --bmc1_ucm_cone_mode                    none
% 3.53/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.53/0.99  --bmc1_ucm_relax_model                  4
% 3.53/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.53/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/0.99  --bmc1_ucm_layered_model                none
% 3.53/0.99  --bmc1_ucm_max_lemma_size               10
% 3.53/0.99  
% 3.53/0.99  ------ AIG Options
% 3.53/0.99  
% 3.53/0.99  --aig_mode                              false
% 3.53/0.99  
% 3.53/0.99  ------ Instantiation Options
% 3.53/0.99  
% 3.53/0.99  --instantiation_flag                    true
% 3.53/0.99  --inst_sos_flag                         false
% 3.53/0.99  --inst_sos_phase                        true
% 3.53/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/0.99  --inst_lit_sel_side                     num_symb
% 3.53/0.99  --inst_solver_per_active                1400
% 3.53/0.99  --inst_solver_calls_frac                1.
% 3.53/0.99  --inst_passive_queue_type               priority_queues
% 3.53/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/0.99  --inst_passive_queues_freq              [25;2]
% 3.53/0.99  --inst_dismatching                      true
% 3.53/0.99  --inst_eager_unprocessed_to_passive     true
% 3.53/0.99  --inst_prop_sim_given                   true
% 3.53/0.99  --inst_prop_sim_new                     false
% 3.53/0.99  --inst_subs_new                         false
% 3.53/0.99  --inst_eq_res_simp                      false
% 3.53/0.99  --inst_subs_given                       false
% 3.53/0.99  --inst_orphan_elimination               true
% 3.53/0.99  --inst_learning_loop_flag               true
% 3.53/0.99  --inst_learning_start                   3000
% 3.53/0.99  --inst_learning_factor                  2
% 3.53/0.99  --inst_start_prop_sim_after_learn       3
% 3.53/0.99  --inst_sel_renew                        solver
% 3.53/0.99  --inst_lit_activity_flag                true
% 3.53/0.99  --inst_restr_to_given                   false
% 3.53/0.99  --inst_activity_threshold               500
% 3.53/0.99  --inst_out_proof                        true
% 3.53/0.99  
% 3.53/0.99  ------ Resolution Options
% 3.53/0.99  
% 3.53/0.99  --resolution_flag                       true
% 3.53/0.99  --res_lit_sel                           adaptive
% 3.53/0.99  --res_lit_sel_side                      none
% 3.53/0.99  --res_ordering                          kbo
% 3.53/0.99  --res_to_prop_solver                    active
% 3.53/0.99  --res_prop_simpl_new                    false
% 3.53/0.99  --res_prop_simpl_given                  true
% 3.53/0.99  --res_passive_queue_type                priority_queues
% 3.53/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/0.99  --res_passive_queues_freq               [15;5]
% 3.53/0.99  --res_forward_subs                      full
% 3.53/0.99  --res_backward_subs                     full
% 3.53/0.99  --res_forward_subs_resolution           true
% 3.53/0.99  --res_backward_subs_resolution          true
% 3.53/0.99  --res_orphan_elimination                true
% 3.53/0.99  --res_time_limit                        2.
% 3.53/0.99  --res_out_proof                         true
% 3.53/0.99  
% 3.53/0.99  ------ Superposition Options
% 3.53/0.99  
% 3.53/0.99  --superposition_flag                    true
% 3.53/0.99  --sup_passive_queue_type                priority_queues
% 3.53/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.53/0.99  --demod_completeness_check              fast
% 3.53/0.99  --demod_use_ground                      true
% 3.53/0.99  --sup_to_prop_solver                    passive
% 3.53/0.99  --sup_prop_simpl_new                    true
% 3.53/0.99  --sup_prop_simpl_given                  true
% 3.53/0.99  --sup_fun_splitting                     false
% 3.53/0.99  --sup_smt_interval                      50000
% 3.53/0.99  
% 3.53/0.99  ------ Superposition Simplification Setup
% 3.53/0.99  
% 3.53/0.99  --sup_indices_passive                   []
% 3.53/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_full_bw                           [BwDemod]
% 3.53/0.99  --sup_immed_triv                        [TrivRules]
% 3.53/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_immed_bw_main                     []
% 3.53/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/0.99  
% 3.53/0.99  ------ Combination Options
% 3.53/0.99  
% 3.53/0.99  --comb_res_mult                         3
% 3.53/0.99  --comb_sup_mult                         2
% 3.53/0.99  --comb_inst_mult                        10
% 3.53/0.99  
% 3.53/0.99  ------ Debug Options
% 3.53/0.99  
% 3.53/0.99  --dbg_backtrace                         false
% 3.53/0.99  --dbg_dump_prop_clauses                 false
% 3.53/0.99  --dbg_dump_prop_clauses_file            -
% 3.53/0.99  --dbg_out_stat                          false
% 3.53/0.99  ------ Parsing...
% 3.53/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/0.99  ------ Proving...
% 3.53/0.99  ------ Problem Properties 
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  clauses                                 20
% 3.53/0.99  conjectures                             5
% 3.53/0.99  EPR                                     3
% 3.53/0.99  Horn                                    18
% 3.53/0.99  unary                                   6
% 3.53/0.99  binary                                  11
% 3.53/0.99  lits                                    38
% 3.53/0.99  lits eq                                 8
% 3.53/0.99  fd_pure                                 0
% 3.53/0.99  fd_pseudo                               0
% 3.53/0.99  fd_cond                                 0
% 3.53/0.99  fd_pseudo_cond                          0
% 3.53/0.99  AC symbols                              0
% 3.53/0.99  
% 3.53/0.99  ------ Schedule dynamic 5 is on 
% 3.53/0.99  
% 3.53/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  ------ 
% 3.53/0.99  Current options:
% 3.53/0.99  ------ 
% 3.53/0.99  
% 3.53/0.99  ------ Input Options
% 3.53/0.99  
% 3.53/0.99  --out_options                           all
% 3.53/0.99  --tptp_safe_out                         true
% 3.53/0.99  --problem_path                          ""
% 3.53/0.99  --include_path                          ""
% 3.53/0.99  --clausifier                            res/vclausify_rel
% 3.53/0.99  --clausifier_options                    --mode clausify
% 3.53/0.99  --stdin                                 false
% 3.53/0.99  --stats_out                             all
% 3.53/0.99  
% 3.53/0.99  ------ General Options
% 3.53/0.99  
% 3.53/0.99  --fof                                   false
% 3.53/0.99  --time_out_real                         305.
% 3.53/0.99  --time_out_virtual                      -1.
% 3.53/0.99  --symbol_type_check                     false
% 3.53/0.99  --clausify_out                          false
% 3.53/0.99  --sig_cnt_out                           false
% 3.53/0.99  --trig_cnt_out                          false
% 3.53/0.99  --trig_cnt_out_tolerance                1.
% 3.53/0.99  --trig_cnt_out_sk_spl                   false
% 3.53/0.99  --abstr_cl_out                          false
% 3.53/0.99  
% 3.53/0.99  ------ Global Options
% 3.53/0.99  
% 3.53/0.99  --schedule                              default
% 3.53/0.99  --add_important_lit                     false
% 3.53/0.99  --prop_solver_per_cl                    1000
% 3.53/0.99  --min_unsat_core                        false
% 3.53/0.99  --soft_assumptions                      false
% 3.53/0.99  --soft_lemma_size                       3
% 3.53/0.99  --prop_impl_unit_size                   0
% 3.53/0.99  --prop_impl_unit                        []
% 3.53/0.99  --share_sel_clauses                     true
% 3.53/0.99  --reset_solvers                         false
% 3.53/0.99  --bc_imp_inh                            [conj_cone]
% 3.53/0.99  --conj_cone_tolerance                   3.
% 3.53/0.99  --extra_neg_conj                        none
% 3.53/0.99  --large_theory_mode                     true
% 3.53/0.99  --prolific_symb_bound                   200
% 3.53/0.99  --lt_threshold                          2000
% 3.53/0.99  --clause_weak_htbl                      true
% 3.53/0.99  --gc_record_bc_elim                     false
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing Options
% 3.53/0.99  
% 3.53/0.99  --preprocessing_flag                    true
% 3.53/0.99  --time_out_prep_mult                    0.1
% 3.53/0.99  --splitting_mode                        input
% 3.53/0.99  --splitting_grd                         true
% 3.53/0.99  --splitting_cvd                         false
% 3.53/0.99  --splitting_cvd_svl                     false
% 3.53/0.99  --splitting_nvd                         32
% 3.53/0.99  --sub_typing                            true
% 3.53/0.99  --prep_gs_sim                           true
% 3.53/0.99  --prep_unflatten                        true
% 3.53/0.99  --prep_res_sim                          true
% 3.53/0.99  --prep_upred                            true
% 3.53/0.99  --prep_sem_filter                       exhaustive
% 3.53/0.99  --prep_sem_filter_out                   false
% 3.53/0.99  --pred_elim                             true
% 3.53/0.99  --res_sim_input                         true
% 3.53/0.99  --eq_ax_congr_red                       true
% 3.53/0.99  --pure_diseq_elim                       true
% 3.53/0.99  --brand_transform                       false
% 3.53/0.99  --non_eq_to_eq                          false
% 3.53/0.99  --prep_def_merge                        true
% 3.53/0.99  --prep_def_merge_prop_impl              false
% 3.53/0.99  --prep_def_merge_mbd                    true
% 3.53/0.99  --prep_def_merge_tr_red                 false
% 3.53/0.99  --prep_def_merge_tr_cl                  false
% 3.53/0.99  --smt_preprocessing                     true
% 3.53/0.99  --smt_ac_axioms                         fast
% 3.53/0.99  --preprocessed_out                      false
% 3.53/0.99  --preprocessed_stats                    false
% 3.53/0.99  
% 3.53/0.99  ------ Abstraction refinement Options
% 3.53/0.99  
% 3.53/0.99  --abstr_ref                             []
% 3.53/0.99  --abstr_ref_prep                        false
% 3.53/0.99  --abstr_ref_until_sat                   false
% 3.53/0.99  --abstr_ref_sig_restrict                funpre
% 3.53/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/0.99  --abstr_ref_under                       []
% 3.53/0.99  
% 3.53/0.99  ------ SAT Options
% 3.53/0.99  
% 3.53/0.99  --sat_mode                              false
% 3.53/0.99  --sat_fm_restart_options                ""
% 3.53/0.99  --sat_gr_def                            false
% 3.53/0.99  --sat_epr_types                         true
% 3.53/0.99  --sat_non_cyclic_types                  false
% 3.53/0.99  --sat_finite_models                     false
% 3.53/0.99  --sat_fm_lemmas                         false
% 3.53/0.99  --sat_fm_prep                           false
% 3.53/0.99  --sat_fm_uc_incr                        true
% 3.53/0.99  --sat_out_model                         small
% 3.53/0.99  --sat_out_clauses                       false
% 3.53/0.99  
% 3.53/0.99  ------ QBF Options
% 3.53/0.99  
% 3.53/0.99  --qbf_mode                              false
% 3.53/0.99  --qbf_elim_univ                         false
% 3.53/0.99  --qbf_dom_inst                          none
% 3.53/0.99  --qbf_dom_pre_inst                      false
% 3.53/0.99  --qbf_sk_in                             false
% 3.53/0.99  --qbf_pred_elim                         true
% 3.53/0.99  --qbf_split                             512
% 3.53/0.99  
% 3.53/0.99  ------ BMC1 Options
% 3.53/0.99  
% 3.53/0.99  --bmc1_incremental                      false
% 3.53/0.99  --bmc1_axioms                           reachable_all
% 3.53/0.99  --bmc1_min_bound                        0
% 3.53/0.99  --bmc1_max_bound                        -1
% 3.53/0.99  --bmc1_max_bound_default                -1
% 3.53/0.99  --bmc1_symbol_reachability              true
% 3.53/0.99  --bmc1_property_lemmas                  false
% 3.53/0.99  --bmc1_k_induction                      false
% 3.53/0.99  --bmc1_non_equiv_states                 false
% 3.53/0.99  --bmc1_deadlock                         false
% 3.53/0.99  --bmc1_ucm                              false
% 3.53/0.99  --bmc1_add_unsat_core                   none
% 3.53/0.99  --bmc1_unsat_core_children              false
% 3.53/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/0.99  --bmc1_out_stat                         full
% 3.53/0.99  --bmc1_ground_init                      false
% 3.53/0.99  --bmc1_pre_inst_next_state              false
% 3.53/0.99  --bmc1_pre_inst_state                   false
% 3.53/0.99  --bmc1_pre_inst_reach_state             false
% 3.53/0.99  --bmc1_out_unsat_core                   false
% 3.53/0.99  --bmc1_aig_witness_out                  false
% 3.53/0.99  --bmc1_verbose                          false
% 3.53/0.99  --bmc1_dump_clauses_tptp                false
% 3.53/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.53/0.99  --bmc1_dump_file                        -
% 3.53/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.53/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.53/0.99  --bmc1_ucm_extend_mode                  1
% 3.53/0.99  --bmc1_ucm_init_mode                    2
% 3.53/0.99  --bmc1_ucm_cone_mode                    none
% 3.53/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.53/0.99  --bmc1_ucm_relax_model                  4
% 3.53/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.53/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/0.99  --bmc1_ucm_layered_model                none
% 3.53/0.99  --bmc1_ucm_max_lemma_size               10
% 3.53/0.99  
% 3.53/0.99  ------ AIG Options
% 3.53/0.99  
% 3.53/0.99  --aig_mode                              false
% 3.53/0.99  
% 3.53/0.99  ------ Instantiation Options
% 3.53/0.99  
% 3.53/0.99  --instantiation_flag                    true
% 3.53/0.99  --inst_sos_flag                         false
% 3.53/0.99  --inst_sos_phase                        true
% 3.53/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/0.99  --inst_lit_sel_side                     none
% 3.53/0.99  --inst_solver_per_active                1400
% 3.53/0.99  --inst_solver_calls_frac                1.
% 3.53/0.99  --inst_passive_queue_type               priority_queues
% 3.53/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/0.99  --inst_passive_queues_freq              [25;2]
% 3.53/0.99  --inst_dismatching                      true
% 3.53/0.99  --inst_eager_unprocessed_to_passive     true
% 3.53/0.99  --inst_prop_sim_given                   true
% 3.53/0.99  --inst_prop_sim_new                     false
% 3.53/0.99  --inst_subs_new                         false
% 3.53/0.99  --inst_eq_res_simp                      false
% 3.53/0.99  --inst_subs_given                       false
% 3.53/0.99  --inst_orphan_elimination               true
% 3.53/0.99  --inst_learning_loop_flag               true
% 3.53/0.99  --inst_learning_start                   3000
% 3.53/0.99  --inst_learning_factor                  2
% 3.53/0.99  --inst_start_prop_sim_after_learn       3
% 3.53/0.99  --inst_sel_renew                        solver
% 3.53/0.99  --inst_lit_activity_flag                true
% 3.53/0.99  --inst_restr_to_given                   false
% 3.53/0.99  --inst_activity_threshold               500
% 3.53/0.99  --inst_out_proof                        true
% 3.53/0.99  
% 3.53/0.99  ------ Resolution Options
% 3.53/0.99  
% 3.53/0.99  --resolution_flag                       false
% 3.53/0.99  --res_lit_sel                           adaptive
% 3.53/0.99  --res_lit_sel_side                      none
% 3.53/0.99  --res_ordering                          kbo
% 3.53/0.99  --res_to_prop_solver                    active
% 3.53/0.99  --res_prop_simpl_new                    false
% 3.53/0.99  --res_prop_simpl_given                  true
% 3.53/0.99  --res_passive_queue_type                priority_queues
% 3.53/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/0.99  --res_passive_queues_freq               [15;5]
% 3.53/0.99  --res_forward_subs                      full
% 3.53/0.99  --res_backward_subs                     full
% 3.53/0.99  --res_forward_subs_resolution           true
% 3.53/0.99  --res_backward_subs_resolution          true
% 3.53/0.99  --res_orphan_elimination                true
% 3.53/0.99  --res_time_limit                        2.
% 3.53/0.99  --res_out_proof                         true
% 3.53/0.99  
% 3.53/0.99  ------ Superposition Options
% 3.53/0.99  
% 3.53/0.99  --superposition_flag                    true
% 3.53/0.99  --sup_passive_queue_type                priority_queues
% 3.53/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.53/0.99  --demod_completeness_check              fast
% 3.53/0.99  --demod_use_ground                      true
% 3.53/0.99  --sup_to_prop_solver                    passive
% 3.53/0.99  --sup_prop_simpl_new                    true
% 3.53/0.99  --sup_prop_simpl_given                  true
% 3.53/0.99  --sup_fun_splitting                     false
% 3.53/0.99  --sup_smt_interval                      50000
% 3.53/0.99  
% 3.53/0.99  ------ Superposition Simplification Setup
% 3.53/0.99  
% 3.53/0.99  --sup_indices_passive                   []
% 3.53/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_full_bw                           [BwDemod]
% 3.53/0.99  --sup_immed_triv                        [TrivRules]
% 3.53/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_immed_bw_main                     []
% 3.53/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/0.99  
% 3.53/0.99  ------ Combination Options
% 3.53/0.99  
% 3.53/0.99  --comb_res_mult                         3
% 3.53/0.99  --comb_sup_mult                         2
% 3.53/0.99  --comb_inst_mult                        10
% 3.53/0.99  
% 3.53/0.99  ------ Debug Options
% 3.53/0.99  
% 3.53/0.99  --dbg_backtrace                         false
% 3.53/0.99  --dbg_dump_prop_clauses                 false
% 3.53/0.99  --dbg_dump_prop_clauses_file            -
% 3.53/0.99  --dbg_out_stat                          false
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  ------ Proving...
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  % SZS status Theorem for theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  fof(f8,axiom,(
% 3.53/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f21,plain,(
% 3.53/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.53/0.99    inference(ennf_transformation,[],[f8])).
% 3.53/0.99  
% 3.53/0.99  fof(f22,plain,(
% 3.53/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.53/0.99    inference(flattening,[],[f21])).
% 3.53/0.99  
% 3.53/0.99  fof(f50,plain,(
% 3.53/0.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f22])).
% 3.53/0.99  
% 3.53/0.99  fof(f14,conjecture,(
% 3.53/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f15,negated_conjecture,(
% 3.53/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 3.53/0.99    inference(negated_conjecture,[],[f14])).
% 3.53/0.99  
% 3.53/0.99  fof(f30,plain,(
% 3.53/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.53/0.99    inference(ennf_transformation,[],[f15])).
% 3.53/0.99  
% 3.53/0.99  fof(f31,plain,(
% 3.53/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.53/0.99    inference(flattening,[],[f30])).
% 3.53/0.99  
% 3.53/0.99  fof(f34,plain,(
% 3.53/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.53/0.99    inference(nnf_transformation,[],[f31])).
% 3.53/0.99  
% 3.53/0.99  fof(f35,plain,(
% 3.53/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.53/0.99    inference(flattening,[],[f34])).
% 3.53/0.99  
% 3.53/0.99  fof(f40,plain,(
% 3.53/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) => ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,sK4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),sK4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,sK4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(X1)))) )),
% 3.53/0.99    introduced(choice_axiom,[])).
% 3.53/0.99  
% 3.53/0.99  fof(f39,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : ((~r1_tarski(sK3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,sK3),X4)) & (r1_tarski(sK3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,sK3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 3.53/0.99    introduced(choice_axiom,[])).
% 3.53/0.99  
% 3.53/0.99  fof(f38,plain,(
% 3.53/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,sK2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,sK2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,sK2,X4)) | r1_tarski(k7_relset_1(X0,X1,sK2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK2,X0,X1) & v1_funct_1(sK2))) )),
% 3.53/0.99    introduced(choice_axiom,[])).
% 3.53/0.99  
% 3.53/0.99  fof(f37,plain,(
% 3.53/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,sK1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,sK1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,sK1,X2,X4)) | r1_tarski(k7_relset_1(X0,sK1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) & v1_funct_2(X2,X0,sK1) & v1_funct_1(X2)) & ~v1_xboole_0(sK1))) )),
% 3.53/0.99    introduced(choice_axiom,[])).
% 3.53/0.99  
% 3.53/0.99  fof(f36,plain,(
% 3.53/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 3.53/0.99    introduced(choice_axiom,[])).
% 3.53/0.99  
% 3.53/0.99  fof(f41,plain,(
% 3.53/0.99    (((((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 3.53/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f35,f40,f39,f38,f37,f36])).
% 3.53/0.99  
% 3.53/0.99  fof(f63,plain,(
% 3.53/0.99    v1_funct_1(sK2)),
% 3.53/0.99    inference(cnf_transformation,[],[f41])).
% 3.53/0.99  
% 3.53/0.99  fof(f65,plain,(
% 3.53/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.53/0.99    inference(cnf_transformation,[],[f41])).
% 3.53/0.99  
% 3.53/0.99  fof(f4,axiom,(
% 3.53/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f32,plain,(
% 3.53/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.53/0.99    inference(nnf_transformation,[],[f4])).
% 3.53/0.99  
% 3.53/0.99  fof(f45,plain,(
% 3.53/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.53/0.99    inference(cnf_transformation,[],[f32])).
% 3.53/0.99  
% 3.53/0.99  fof(f5,axiom,(
% 3.53/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f18,plain,(
% 3.53/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.53/0.99    inference(ennf_transformation,[],[f5])).
% 3.53/0.99  
% 3.53/0.99  fof(f47,plain,(
% 3.53/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f18])).
% 3.53/0.99  
% 3.53/0.99  fof(f46,plain,(
% 3.53/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f32])).
% 3.53/0.99  
% 3.53/0.99  fof(f6,axiom,(
% 3.53/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f48,plain,(
% 3.53/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.53/0.99    inference(cnf_transformation,[],[f6])).
% 3.53/0.99  
% 3.53/0.99  fof(f12,axiom,(
% 3.53/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f27,plain,(
% 3.53/0.99    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/0.99    inference(ennf_transformation,[],[f12])).
% 3.53/0.99  
% 3.53/0.99  fof(f54,plain,(
% 3.53/0.99    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/0.99    inference(cnf_transformation,[],[f27])).
% 3.53/0.99  
% 3.53/0.99  fof(f68,plain,(
% 3.53/0.99    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 3.53/0.99    inference(cnf_transformation,[],[f41])).
% 3.53/0.99  
% 3.53/0.99  fof(f3,axiom,(
% 3.53/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f17,plain,(
% 3.53/0.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.53/0.99    inference(ennf_transformation,[],[f3])).
% 3.53/0.99  
% 3.53/0.99  fof(f44,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f17])).
% 3.53/0.99  
% 3.53/0.99  fof(f66,plain,(
% 3.53/0.99    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 3.53/0.99    inference(cnf_transformation,[],[f41])).
% 3.53/0.99  
% 3.53/0.99  fof(f11,axiom,(
% 3.53/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f26,plain,(
% 3.53/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/0.99    inference(ennf_transformation,[],[f11])).
% 3.53/0.99  
% 3.53/0.99  fof(f53,plain,(
% 3.53/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/0.99    inference(cnf_transformation,[],[f26])).
% 3.53/0.99  
% 3.53/0.99  fof(f13,axiom,(
% 3.53/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f28,plain,(
% 3.53/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/0.99    inference(ennf_transformation,[],[f13])).
% 3.53/0.99  
% 3.53/0.99  fof(f29,plain,(
% 3.53/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/0.99    inference(flattening,[],[f28])).
% 3.53/0.99  
% 3.53/0.99  fof(f33,plain,(
% 3.53/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/0.99    inference(nnf_transformation,[],[f29])).
% 3.53/0.99  
% 3.53/0.99  fof(f55,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/0.99    inference(cnf_transformation,[],[f33])).
% 3.53/0.99  
% 3.53/0.99  fof(f64,plain,(
% 3.53/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.53/0.99    inference(cnf_transformation,[],[f41])).
% 3.53/0.99  
% 3.53/0.99  fof(f10,axiom,(
% 3.53/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f25,plain,(
% 3.53/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/0.99    inference(ennf_transformation,[],[f10])).
% 3.53/0.99  
% 3.53/0.99  fof(f52,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/0.99    inference(cnf_transformation,[],[f25])).
% 3.53/0.99  
% 3.53/0.99  fof(f1,axiom,(
% 3.53/0.99    v1_xboole_0(k1_xboole_0)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f42,plain,(
% 3.53/0.99    v1_xboole_0(k1_xboole_0)),
% 3.53/0.99    inference(cnf_transformation,[],[f1])).
% 3.53/0.99  
% 3.53/0.99  fof(f62,plain,(
% 3.53/0.99    ~v1_xboole_0(sK1)),
% 3.53/0.99    inference(cnf_transformation,[],[f41])).
% 3.53/0.99  
% 3.53/0.99  fof(f9,axiom,(
% 3.53/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f23,plain,(
% 3.53/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.53/0.99    inference(ennf_transformation,[],[f9])).
% 3.53/0.99  
% 3.53/0.99  fof(f24,plain,(
% 3.53/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.53/0.99    inference(flattening,[],[f23])).
% 3.53/0.99  
% 3.53/0.99  fof(f51,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f24])).
% 3.53/0.99  
% 3.53/0.99  fof(f7,axiom,(
% 3.53/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f19,plain,(
% 3.53/0.99    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 3.53/0.99    inference(ennf_transformation,[],[f7])).
% 3.53/0.99  
% 3.53/0.99  fof(f20,plain,(
% 3.53/0.99    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 3.53/0.99    inference(flattening,[],[f19])).
% 3.53/0.99  
% 3.53/0.99  fof(f49,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f20])).
% 3.53/0.99  
% 3.53/0.99  fof(f2,axiom,(
% 3.53/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f16,plain,(
% 3.53/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 3.53/0.99    inference(ennf_transformation,[],[f2])).
% 3.53/0.99  
% 3.53/0.99  fof(f43,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f16])).
% 3.53/0.99  
% 3.53/0.99  fof(f69,plain,(
% 3.53/0.99    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 3.53/0.99    inference(cnf_transformation,[],[f41])).
% 3.53/0.99  
% 3.53/0.99  cnf(c_8,plain,
% 3.53/0.99      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.53/0.99      | ~ v1_funct_1(X0)
% 3.53/0.99      | ~ v1_relat_1(X0) ),
% 3.53/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_25,negated_conjecture,
% 3.53/0.99      ( v1_funct_1(sK2) ),
% 3.53/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_383,plain,
% 3.53/0.99      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.53/0.99      | ~ v1_relat_1(X0)
% 3.53/0.99      | sK2 != X0 ),
% 3.53/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_384,plain,
% 3.53/0.99      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
% 3.53/0.99      | ~ v1_relat_1(sK2) ),
% 3.53/0.99      inference(unflattening,[status(thm)],[c_383]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1834,plain,
% 3.53/0.99      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) = iProver_top
% 3.53/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_384]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_23,negated_conjecture,
% 3.53/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.53/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_32,plain,
% 3.53/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_385,plain,
% 3.53/0.99      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) = iProver_top
% 3.53/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_384]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_4,plain,
% 3.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.53/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1974,plain,
% 3.53/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.53/0.99      | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1975,plain,
% 3.53/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.53/0.99      | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_1974]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_5,plain,
% 3.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.53/0.99      | ~ v1_relat_1(X1)
% 3.53/0.99      | v1_relat_1(X0) ),
% 3.53/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3,plain,
% 3.53/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.53/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_213,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.53/0.99      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_214,plain,
% 3.53/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.53/0.99      inference(renaming,[status(thm)],[c_213]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_271,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.53/0.99      inference(bin_hyper_res,[status(thm)],[c_5,c_214]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1977,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.53/0.99      | v1_relat_1(X0)
% 3.53/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_271]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2295,plain,
% 3.53/0.99      ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
% 3.53/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.53/0.99      | v1_relat_1(sK2) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_1977]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2296,plain,
% 3.53/0.99      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.53/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.53/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_2295]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_6,plain,
% 3.53/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.53/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2344,plain,
% 3.53/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2345,plain,
% 3.53/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_2344]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2386,plain,
% 3.53/0.99      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) = iProver_top ),
% 3.53/0.99      inference(global_propositional_subsumption,
% 3.53/0.99                [status(thm)],
% 3.53/0.99                [c_1834,c_32,c_385,c_1975,c_2296,c_2345]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1836,plain,
% 3.53/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1846,plain,
% 3.53/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.53/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2172,plain,
% 3.53/0.99      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_1836,c_1846]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1835,plain,
% 3.53/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.53/0.99      | v1_relat_1(X1) != iProver_top
% 3.53/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_271]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2562,plain,
% 3.53/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.53/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_2172,c_1835]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3634,plain,
% 3.53/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.53/0.99      inference(global_propositional_subsumption,
% 3.53/0.99                [status(thm)],
% 3.53/0.99                [c_2562,c_32,c_1975,c_2296,c_2345]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_12,plain,
% 3.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.53/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1841,plain,
% 3.53/0.99      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.53/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2708,plain,
% 3.53/0.99      ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_1836,c_1841]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_20,negated_conjecture,
% 3.53/0.99      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
% 3.53/0.99      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
% 3.53/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1839,plain,
% 3.53/0.99      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
% 3.53/0.99      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.53/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1848,plain,
% 3.53/0.99      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2165,plain,
% 3.53/0.99      ( k2_xboole_0(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = sK4
% 3.53/0.99      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_1839,c_1848]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2863,plain,
% 3.53/0.99      ( k2_xboole_0(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = sK4
% 3.53/0.99      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
% 3.53/0.99      inference(demodulation,[status(thm)],[c_2708,c_2165]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_22,negated_conjecture,
% 3.53/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 3.53/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_33,plain,
% 3.53/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1971,plain,
% 3.53/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) | r1_tarski(sK3,sK0) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1972,plain,
% 3.53/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 3.53/0.99      | r1_tarski(sK3,sK0) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_1971]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2864,plain,
% 3.53/0.99      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
% 3.53/0.99      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
% 3.53/0.99      inference(demodulation,[status(thm)],[c_2708,c_1839]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_11,plain,
% 3.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.53/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1842,plain,
% 3.53/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.53/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2803,plain,
% 3.53/1.00      ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1836,c_1842]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3026,plain,
% 3.53/1.00      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
% 3.53/1.00      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_2864,c_2803]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_18,plain,
% 3.53/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.53/1.00      | k1_xboole_0 = X2 ),
% 3.53/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_24,negated_conjecture,
% 3.53/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_453,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.53/1.00      | sK2 != X0
% 3.53/1.00      | sK1 != X2
% 3.53/1.00      | sK0 != X1
% 3.53/1.00      | k1_xboole_0 = X2 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_454,plain,
% 3.53/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.53/1.00      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.53/1.00      | k1_xboole_0 = sK1 ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_453]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_456,plain,
% 3.53/1.00      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_454,c_23]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_10,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1843,plain,
% 3.53/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.53/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2694,plain,
% 3.53/1.00      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1836,c_1843]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2815,plain,
% 3.53/1.00      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_456,c_2694]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_0,plain,
% 3.53/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_26,negated_conjecture,
% 3.53/1.00      ( ~ v1_xboole_0(sK1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_373,plain,
% 3.53/1.00      ( sK1 != k1_xboole_0 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_26]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2932,plain,
% 3.53/1.00      ( k1_relat_1(sK2) = sK0 ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_2815,c_373]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9,plain,
% 3.53/1.00      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 3.53/1.00      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.53/1.00      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 3.53/1.00      | ~ v1_funct_1(X1)
% 3.53/1.00      | ~ v1_relat_1(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_395,plain,
% 3.53/1.00      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 3.53/1.00      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.53/1.00      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 3.53/1.00      | ~ v1_relat_1(X1)
% 3.53/1.00      | sK2 != X1 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_396,plain,
% 3.53/1.00      ( r1_tarski(X0,k10_relat_1(sK2,X1))
% 3.53/1.00      | ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.53/1.00      | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
% 3.53/1.00      | ~ v1_relat_1(sK2) ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_395]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1833,plain,
% 3.53/1.00      ( r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top
% 3.53/1.00      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 3.53/1.00      | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top
% 3.53/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2936,plain,
% 3.53/1.00      ( r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top
% 3.53/1.00      | r1_tarski(X0,sK0) != iProver_top
% 3.53/1.00      | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top
% 3.53/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_2932,c_1833]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3779,plain,
% 3.53/1.00      ( r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top
% 3.53/1.00      | r1_tarski(X0,sK0) != iProver_top
% 3.53/1.00      | r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_2936,c_32,c_1975,c_2296,c_2345]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3780,plain,
% 3.53/1.00      ( r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top
% 3.53/1.00      | r1_tarski(X0,sK0) != iProver_top
% 3.53/1.00      | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_3779]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3790,plain,
% 3.53/1.00      ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top
% 3.53/1.00      | r1_tarski(sK3,sK0) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_3026,c_3780]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3825,plain,
% 3.53/1.00      ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_2863,c_33,c_1972,c_3790]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7,plain,
% 3.53/1.00      ( ~ r1_tarski(X0,X1)
% 3.53/1.00      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 3.53/1.00      | ~ v1_relat_1(X2) ),
% 3.53/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1844,plain,
% 3.53/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.53/1.00      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
% 3.53/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3168,plain,
% 3.53/1.00      ( k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,X2)
% 3.53/1.00      | r1_tarski(X1,X2) != iProver_top
% 3.53/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1844,c_1848]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7133,plain,
% 3.53/1.00      ( k2_xboole_0(k9_relat_1(X0,sK3),k9_relat_1(X0,k10_relat_1(sK2,sK4))) = k9_relat_1(X0,k10_relat_1(sK2,sK4))
% 3.53/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_3825,c_3168]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9452,plain,
% 3.53/1.00      ( k2_xboole_0(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) = k9_relat_1(sK2,k10_relat_1(sK2,sK4)) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_3634,c_7133]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1,plain,
% 3.53/1.00      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1849,plain,
% 3.53/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.53/1.00      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9610,plain,
% 3.53/1.00      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK4)),X0) != iProver_top
% 3.53/1.00      | r1_tarski(k9_relat_1(sK2,sK3),X0) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_9452,c_1849]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9790,plain,
% 3.53/1.00      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2386,c_9610]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_19,negated_conjecture,
% 3.53/1.00      ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
% 3.53/1.00      | ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1840,plain,
% 3.53/1.00      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
% 3.53/1.00      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2865,plain,
% 3.53/1.00      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
% 3.53/1.00      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_2708,c_1840]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2928,plain,
% 3.53/1.00      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top
% 3.53/1.00      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_2865,c_2803]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(contradiction,plain,
% 3.53/1.00      ( $false ),
% 3.53/1.00      inference(minisat,[status(thm)],[c_9790,c_3790,c_2928,c_1972,c_33]) ).
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  ------                               Statistics
% 3.53/1.00  
% 3.53/1.00  ------ General
% 3.53/1.00  
% 3.53/1.00  abstr_ref_over_cycles:                  0
% 3.53/1.00  abstr_ref_under_cycles:                 0
% 3.53/1.00  gc_basic_clause_elim:                   0
% 3.53/1.00  forced_gc_time:                         0
% 3.53/1.00  parsing_time:                           0.012
% 3.53/1.00  unif_index_cands_time:                  0.
% 3.53/1.00  unif_index_add_time:                    0.
% 3.53/1.00  orderings_time:                         0.
% 3.53/1.00  out_proof_time:                         0.011
% 3.53/1.00  total_time:                             0.315
% 3.53/1.00  num_of_symbols:                         52
% 3.53/1.00  num_of_terms:                           11571
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing
% 3.53/1.00  
% 3.53/1.00  num_of_splits:                          0
% 3.53/1.00  num_of_split_atoms:                     0
% 3.53/1.00  num_of_reused_defs:                     0
% 3.53/1.00  num_eq_ax_congr_red:                    17
% 3.53/1.00  num_of_sem_filtered_clauses:            1
% 3.53/1.00  num_of_subtypes:                        0
% 3.53/1.00  monotx_restored_types:                  0
% 3.53/1.00  sat_num_of_epr_types:                   0
% 3.53/1.00  sat_num_of_non_cyclic_types:            0
% 3.53/1.00  sat_guarded_non_collapsed_types:        0
% 3.53/1.00  num_pure_diseq_elim:                    0
% 3.53/1.00  simp_replaced_by:                       0
% 3.53/1.00  res_preprocessed:                       138
% 3.53/1.00  prep_upred:                             0
% 3.53/1.00  prep_unflattend:                        74
% 3.53/1.00  smt_new_axioms:                         0
% 3.53/1.00  pred_elim_cands:                        3
% 3.53/1.00  pred_elim:                              3
% 3.53/1.00  pred_elim_cl:                           8
% 3.53/1.00  pred_elim_cycles:                       7
% 3.53/1.00  merged_defs:                            20
% 3.53/1.00  merged_defs_ncl:                        0
% 3.53/1.00  bin_hyper_res:                          21
% 3.53/1.00  prep_cycles:                            5
% 3.53/1.00  pred_elim_time:                         0.023
% 3.53/1.00  splitting_time:                         0.
% 3.53/1.00  sem_filter_time:                        0.
% 3.53/1.00  monotx_time:                            0.
% 3.53/1.00  subtype_inf_time:                       0.
% 3.53/1.00  
% 3.53/1.00  ------ Problem properties
% 3.53/1.00  
% 3.53/1.00  clauses:                                20
% 3.53/1.00  conjectures:                            5
% 3.53/1.00  epr:                                    3
% 3.53/1.00  horn:                                   18
% 3.53/1.00  ground:                                 8
% 3.53/1.00  unary:                                  6
% 3.53/1.00  binary:                                 11
% 3.53/1.00  lits:                                   38
% 3.53/1.00  lits_eq:                                8
% 3.53/1.00  fd_pure:                                0
% 3.53/1.00  fd_pseudo:                              0
% 3.53/1.00  fd_cond:                                0
% 3.53/1.00  fd_pseudo_cond:                         0
% 3.53/1.00  ac_symbols:                             0
% 3.53/1.00  
% 3.53/1.00  ------ Propositional Solver
% 3.53/1.00  
% 3.53/1.00  prop_solver_calls:                      33
% 3.53/1.00  prop_fast_solver_calls:                 965
% 3.53/1.00  smt_solver_calls:                       0
% 3.53/1.00  smt_fast_solver_calls:                  0
% 3.53/1.00  prop_num_of_clauses:                    4213
% 3.53/1.00  prop_preprocess_simplified:             7231
% 3.53/1.00  prop_fo_subsumed:                       17
% 3.53/1.00  prop_solver_time:                       0.
% 3.53/1.00  smt_solver_time:                        0.
% 3.53/1.00  smt_fast_solver_time:                   0.
% 3.53/1.00  prop_fast_solver_time:                  0.
% 3.53/1.00  prop_unsat_core_time:                   0.
% 3.53/1.00  
% 3.53/1.00  ------ QBF
% 3.53/1.00  
% 3.53/1.00  qbf_q_res:                              0
% 3.53/1.00  qbf_num_tautologies:                    0
% 3.53/1.00  qbf_prep_cycles:                        0
% 3.53/1.00  
% 3.53/1.00  ------ BMC1
% 3.53/1.00  
% 3.53/1.00  bmc1_current_bound:                     -1
% 3.53/1.00  bmc1_last_solved_bound:                 -1
% 3.53/1.00  bmc1_unsat_core_size:                   -1
% 3.53/1.00  bmc1_unsat_core_parents_size:           -1
% 3.53/1.00  bmc1_merge_next_fun:                    0
% 3.53/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.53/1.00  
% 3.53/1.00  ------ Instantiation
% 3.53/1.00  
% 3.53/1.00  inst_num_of_clauses:                    1060
% 3.53/1.00  inst_num_in_passive:                    155
% 3.53/1.00  inst_num_in_active:                     434
% 3.53/1.00  inst_num_in_unprocessed:                471
% 3.53/1.00  inst_num_of_loops:                      540
% 3.53/1.00  inst_num_of_learning_restarts:          0
% 3.53/1.00  inst_num_moves_active_passive:          102
% 3.53/1.00  inst_lit_activity:                      0
% 3.53/1.00  inst_lit_activity_moves:                0
% 3.53/1.00  inst_num_tautologies:                   0
% 3.53/1.00  inst_num_prop_implied:                  0
% 3.53/1.00  inst_num_existing_simplified:           0
% 3.53/1.00  inst_num_eq_res_simplified:             0
% 3.53/1.00  inst_num_child_elim:                    0
% 3.53/1.00  inst_num_of_dismatching_blockings:      241
% 3.53/1.00  inst_num_of_non_proper_insts:           774
% 3.53/1.00  inst_num_of_duplicates:                 0
% 3.53/1.00  inst_inst_num_from_inst_to_res:         0
% 3.53/1.00  inst_dismatching_checking_time:         0.
% 3.53/1.00  
% 3.53/1.00  ------ Resolution
% 3.53/1.00  
% 3.53/1.00  res_num_of_clauses:                     0
% 3.53/1.00  res_num_in_passive:                     0
% 3.53/1.00  res_num_in_active:                      0
% 3.53/1.00  res_num_of_loops:                       143
% 3.53/1.00  res_forward_subset_subsumed:            50
% 3.53/1.00  res_backward_subset_subsumed:           0
% 3.53/1.00  res_forward_subsumed:                   0
% 3.53/1.00  res_backward_subsumed:                  0
% 3.53/1.00  res_forward_subsumption_resolution:     0
% 3.53/1.00  res_backward_subsumption_resolution:    0
% 3.53/1.00  res_clause_to_clause_subsumption:       1300
% 3.53/1.00  res_orphan_elimination:                 0
% 3.53/1.00  res_tautology_del:                      132
% 3.53/1.00  res_num_eq_res_simplified:              0
% 3.53/1.00  res_num_sel_changes:                    0
% 3.53/1.00  res_moves_from_active_to_pass:          0
% 3.53/1.00  
% 3.53/1.00  ------ Superposition
% 3.53/1.00  
% 3.53/1.00  sup_time_total:                         0.
% 3.53/1.00  sup_time_generating:                    0.
% 3.53/1.00  sup_time_sim_full:                      0.
% 3.53/1.00  sup_time_sim_immed:                     0.
% 3.53/1.00  
% 3.53/1.00  sup_num_of_clauses:                     291
% 3.53/1.00  sup_num_in_active:                      99
% 3.53/1.00  sup_num_in_passive:                     192
% 3.53/1.00  sup_num_of_loops:                       106
% 3.53/1.00  sup_fw_superposition:                   150
% 3.53/1.00  sup_bw_superposition:                   151
% 3.53/1.00  sup_immediate_simplified:               7
% 3.53/1.00  sup_given_eliminated:                   0
% 3.53/1.00  comparisons_done:                       0
% 3.53/1.00  comparisons_avoided:                    0
% 3.53/1.00  
% 3.53/1.00  ------ Simplifications
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  sim_fw_subset_subsumed:                 5
% 3.53/1.00  sim_bw_subset_subsumed:                 5
% 3.53/1.00  sim_fw_subsumed:                        1
% 3.53/1.00  sim_bw_subsumed:                        0
% 3.53/1.00  sim_fw_subsumption_res:                 0
% 3.53/1.00  sim_bw_subsumption_res:                 0
% 3.53/1.00  sim_tautology_del:                      3
% 3.53/1.00  sim_eq_tautology_del:                   1
% 3.53/1.00  sim_eq_res_simp:                        0
% 3.53/1.00  sim_fw_demodulated:                     6
% 3.53/1.00  sim_bw_demodulated:                     5
% 3.53/1.00  sim_light_normalised:                   1
% 3.53/1.00  sim_joinable_taut:                      0
% 3.53/1.00  sim_joinable_simp:                      0
% 3.53/1.00  sim_ac_normalised:                      0
% 3.53/1.00  sim_smt_subsumption:                    0
% 3.53/1.00  
%------------------------------------------------------------------------------

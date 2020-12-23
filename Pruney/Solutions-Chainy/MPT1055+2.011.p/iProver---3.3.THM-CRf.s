%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:09 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  144 (1952 expanded)
%              Number of clauses        :   88 ( 550 expanded)
%              Number of leaves         :   17 ( 607 expanded)
%              Depth                    :   23
%              Number of atoms          :  462 (15249 expanded)
%              Number of equality atoms :  126 ( 690 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f32,f37,f36,f35,f34,f33])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f53,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1454,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1908,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1454])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1460,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k7_relset_1(X1_47,X2_47,X0_47,X3_47) = k9_relat_1(X0_47,X3_47) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1902,plain,
    ( k7_relset_1(X0_47,X1_47,X2_47,X3_47) = k9_relat_1(X2_47,X3_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1460])).

cnf(c_2778,plain,
    ( k7_relset_1(sK0,sK1,sK2,X0_47) = k9_relat_1(sK2,X0_47) ),
    inference(superposition,[status(thm)],[c_1908,c_1902])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1457,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1905,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1457])).

cnf(c_2855,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2778,c_1905])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1459,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k8_relset_1(X1_47,X2_47,X0_47,X3_47) = k10_relat_1(X0_47,X3_47) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1903,plain,
    ( k8_relset_1(X0_47,X1_47,X2_47,X3_47) = k10_relat_1(X2_47,X3_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1459])).

cnf(c_2841,plain,
    ( k8_relset_1(sK0,sK1,sK2,X0_47) = k10_relat_1(sK2,X0_47) ),
    inference(superposition,[status(thm)],[c_1908,c_1903])).

cnf(c_3123,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2855,c_2841])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1466,plain,
    ( ~ r1_tarski(X0_47,X1_47)
    | ~ r1_tarski(X2_47,X0_47)
    | r1_tarski(X2_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1896,plain,
    ( r1_tarski(X0_47,X1_47) != iProver_top
    | r1_tarski(X2_47,X0_47) != iProver_top
    | r1_tarski(X2_47,X1_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1466])).

cnf(c_3128,plain,
    ( r1_tarski(X0_47,k9_relat_1(sK2,sK3)) != iProver_top
    | r1_tarski(X0_47,sK4) = iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3123,c_1896])).

cnf(c_26,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1461,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2016,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1461])).

cnf(c_2017,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2016])).

cnf(c_7,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_336,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_337,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,X1))
    | ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_1449,plain,
    ( r1_tarski(X0_47,k10_relat_1(sK2,X1_47))
    | ~ r1_tarski(X0_47,k1_relat_1(sK2))
    | ~ r1_tarski(k9_relat_1(sK2,X0_47),X1_47)
    | ~ v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_337])).

cnf(c_1910,plain,
    ( r1_tarski(X0_47,k10_relat_1(sK2,X1_47)) = iProver_top
    | r1_tarski(X0_47,k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_47),X1_47) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1449])).

cnf(c_1512,plain,
    ( r1_tarski(X0_47,k10_relat_1(sK2,X1_47)) = iProver_top
    | r1_tarski(X0_47,k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_47),X1_47) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1449])).

cnf(c_2713,plain,
    ( r1_tarski(k9_relat_1(sK2,X0_47),X1_47) != iProver_top
    | r1_tarski(X0_47,k1_relat_1(sK2)) != iProver_top
    | r1_tarski(X0_47,k10_relat_1(sK2,X1_47)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1910,c_26,c_1512,c_2017])).

cnf(c_2714,plain,
    ( r1_tarski(X0_47,k10_relat_1(sK2,X1_47)) = iProver_top
    | r1_tarski(X0_47,k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_47),X1_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_2713])).

cnf(c_3127,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top
    | r1_tarski(sK3,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3123,c_2714])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = X1
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_311,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_313,plain,
    ( k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_311,c_19,c_17])).

cnf(c_1451,plain,
    ( k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) = sK0
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_313])).

cnf(c_2857,plain,
    ( k8_relset_1(sK0,sK1,sK2,k9_relat_1(sK2,sK0)) = sK0
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2778,c_1451])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_20,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_809,plain,
    ( sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_1453,plain,
    ( sK1 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_809])).

cnf(c_3117,plain,
    ( k8_relset_1(sK0,sK1,sK2,k9_relat_1(sK2,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2857,c_1453])).

cnf(c_3120,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_2841,c_3117])).

cnf(c_5,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1462,plain,
    ( r1_tarski(k10_relat_1(X0_47,X1_47),k1_relat_1(X0_47))
    | ~ v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1900,plain,
    ( r1_tarski(k10_relat_1(X0_47,X1_47),k1_relat_1(X0_47)) = iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1462])).

cnf(c_3235,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3120,c_1900])).

cnf(c_6,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_324,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_19])).

cnf(c_325,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_1450,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_47)),X0_47)
    | ~ v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_325])).

cnf(c_1909,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_47)),X0_47) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1450])).

cnf(c_1511,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_47)),X0_47) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1450])).

cnf(c_2629,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_47)),X0_47) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1909,c_26,c_1511,c_2017])).

cnf(c_3234,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3120,c_2629])).

cnf(c_3246,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) = iProver_top
    | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3234,c_2714])).

cnf(c_3250,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top
    | r1_tarski(sK0,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3246,c_3120])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1455,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1907,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1455])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1464,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
    | r1_tarski(X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1898,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(X1_47)) != iProver_top
    | r1_tarski(X0_47,X1_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1464])).

cnf(c_2274,plain,
    ( r1_tarski(sK3,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1907,c_1898])).

cnf(c_3553,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3235,c_26,c_2017])).

cnf(c_3558,plain,
    ( r1_tarski(X0_47,k1_relat_1(sK2)) = iProver_top
    | r1_tarski(X0_47,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3553,c_1896])).

cnf(c_3644,plain,
    ( r1_tarski(X0_47,X1_47) != iProver_top
    | r1_tarski(X0_47,k1_relat_1(sK2)) = iProver_top
    | r1_tarski(X1_47,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3558,c_1896])).

cnf(c_5792,plain,
    ( r1_tarski(sK0,sK0) != iProver_top
    | r1_tarski(sK3,k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2274,c_3644])).

cnf(c_6218,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3128,c_26,c_2017,c_3127,c_3235,c_3250,c_5792])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1463,plain,
    ( ~ r1_tarski(X0_47,X1_47)
    | r1_tarski(k9_relat_1(X2_47,X0_47),k9_relat_1(X2_47,X1_47))
    | ~ v1_relat_1(X2_47) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1899,plain,
    ( r1_tarski(X0_47,X1_47) != iProver_top
    | r1_tarski(k9_relat_1(X2_47,X0_47),k9_relat_1(X2_47,X1_47)) = iProver_top
    | v1_relat_1(X2_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1463])).

cnf(c_2636,plain,
    ( r1_tarski(X0_47,X1_47) = iProver_top
    | r1_tarski(X0_47,k9_relat_1(sK2,k10_relat_1(sK2,X1_47))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2629,c_1896])).

cnf(c_3857,plain,
    ( r1_tarski(X0_47,k10_relat_1(sK2,X1_47)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_47),X1_47) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1899,c_2636])).

cnf(c_9689,plain,
    ( r1_tarski(k9_relat_1(sK2,X0_47),X1_47) = iProver_top
    | r1_tarski(X0_47,k10_relat_1(sK2,X1_47)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3857,c_26,c_2017])).

cnf(c_9690,plain,
    ( r1_tarski(X0_47,k10_relat_1(sK2,X1_47)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_47),X1_47) = iProver_top ),
    inference(renaming,[status(thm)],[c_9689])).

cnf(c_9701,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6218,c_9690])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1458,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1904,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1458])).

cnf(c_2856,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2778,c_1904])).

cnf(c_3059,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2856,c_2841])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9701,c_5792,c_3250,c_3235,c_3127,c_3059,c_2017,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:01:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.40/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.01  
% 2.40/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.40/1.01  
% 2.40/1.01  ------  iProver source info
% 2.40/1.01  
% 2.40/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.40/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.40/1.01  git: non_committed_changes: false
% 2.40/1.01  git: last_make_outside_of_git: false
% 2.40/1.01  
% 2.40/1.01  ------ 
% 2.40/1.01  
% 2.40/1.01  ------ Input Options
% 2.40/1.01  
% 2.40/1.01  --out_options                           all
% 2.40/1.01  --tptp_safe_out                         true
% 2.40/1.01  --problem_path                          ""
% 2.40/1.01  --include_path                          ""
% 2.40/1.01  --clausifier                            res/vclausify_rel
% 2.40/1.01  --clausifier_options                    --mode clausify
% 2.40/1.01  --stdin                                 false
% 2.40/1.01  --stats_out                             all
% 2.40/1.01  
% 2.40/1.01  ------ General Options
% 2.40/1.01  
% 2.40/1.01  --fof                                   false
% 2.40/1.01  --time_out_real                         305.
% 2.40/1.01  --time_out_virtual                      -1.
% 2.40/1.01  --symbol_type_check                     false
% 2.40/1.01  --clausify_out                          false
% 2.40/1.01  --sig_cnt_out                           false
% 2.40/1.01  --trig_cnt_out                          false
% 2.40/1.01  --trig_cnt_out_tolerance                1.
% 2.40/1.01  --trig_cnt_out_sk_spl                   false
% 2.40/1.01  --abstr_cl_out                          false
% 2.40/1.01  
% 2.40/1.01  ------ Global Options
% 2.40/1.01  
% 2.40/1.01  --schedule                              default
% 2.40/1.01  --add_important_lit                     false
% 2.40/1.01  --prop_solver_per_cl                    1000
% 2.40/1.01  --min_unsat_core                        false
% 2.40/1.01  --soft_assumptions                      false
% 2.40/1.01  --soft_lemma_size                       3
% 2.40/1.01  --prop_impl_unit_size                   0
% 2.40/1.01  --prop_impl_unit                        []
% 2.40/1.01  --share_sel_clauses                     true
% 2.40/1.01  --reset_solvers                         false
% 2.40/1.01  --bc_imp_inh                            [conj_cone]
% 2.40/1.01  --conj_cone_tolerance                   3.
% 2.40/1.01  --extra_neg_conj                        none
% 2.40/1.01  --large_theory_mode                     true
% 2.40/1.01  --prolific_symb_bound                   200
% 2.40/1.01  --lt_threshold                          2000
% 2.40/1.01  --clause_weak_htbl                      true
% 2.40/1.01  --gc_record_bc_elim                     false
% 2.40/1.01  
% 2.40/1.01  ------ Preprocessing Options
% 2.40/1.01  
% 2.40/1.01  --preprocessing_flag                    true
% 2.40/1.01  --time_out_prep_mult                    0.1
% 2.40/1.01  --splitting_mode                        input
% 2.40/1.01  --splitting_grd                         true
% 2.40/1.01  --splitting_cvd                         false
% 2.40/1.01  --splitting_cvd_svl                     false
% 2.40/1.01  --splitting_nvd                         32
% 2.40/1.01  --sub_typing                            true
% 2.40/1.01  --prep_gs_sim                           true
% 2.40/1.01  --prep_unflatten                        true
% 2.40/1.01  --prep_res_sim                          true
% 2.40/1.01  --prep_upred                            true
% 2.40/1.01  --prep_sem_filter                       exhaustive
% 2.40/1.01  --prep_sem_filter_out                   false
% 2.40/1.01  --pred_elim                             true
% 2.40/1.01  --res_sim_input                         true
% 2.40/1.01  --eq_ax_congr_red                       true
% 2.40/1.01  --pure_diseq_elim                       true
% 2.40/1.01  --brand_transform                       false
% 2.40/1.01  --non_eq_to_eq                          false
% 2.40/1.01  --prep_def_merge                        true
% 2.40/1.01  --prep_def_merge_prop_impl              false
% 2.40/1.01  --prep_def_merge_mbd                    true
% 2.40/1.01  --prep_def_merge_tr_red                 false
% 2.40/1.01  --prep_def_merge_tr_cl                  false
% 2.40/1.01  --smt_preprocessing                     true
% 2.40/1.01  --smt_ac_axioms                         fast
% 2.40/1.01  --preprocessed_out                      false
% 2.40/1.01  --preprocessed_stats                    false
% 2.40/1.01  
% 2.40/1.01  ------ Abstraction refinement Options
% 2.40/1.01  
% 2.40/1.01  --abstr_ref                             []
% 2.40/1.01  --abstr_ref_prep                        false
% 2.40/1.01  --abstr_ref_until_sat                   false
% 2.40/1.01  --abstr_ref_sig_restrict                funpre
% 2.40/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/1.01  --abstr_ref_under                       []
% 2.40/1.01  
% 2.40/1.01  ------ SAT Options
% 2.40/1.01  
% 2.40/1.01  --sat_mode                              false
% 2.40/1.01  --sat_fm_restart_options                ""
% 2.40/1.01  --sat_gr_def                            false
% 2.40/1.01  --sat_epr_types                         true
% 2.40/1.01  --sat_non_cyclic_types                  false
% 2.40/1.01  --sat_finite_models                     false
% 2.40/1.01  --sat_fm_lemmas                         false
% 2.40/1.01  --sat_fm_prep                           false
% 2.40/1.01  --sat_fm_uc_incr                        true
% 2.40/1.01  --sat_out_model                         small
% 2.40/1.01  --sat_out_clauses                       false
% 2.40/1.01  
% 2.40/1.01  ------ QBF Options
% 2.40/1.01  
% 2.40/1.01  --qbf_mode                              false
% 2.40/1.01  --qbf_elim_univ                         false
% 2.40/1.01  --qbf_dom_inst                          none
% 2.40/1.01  --qbf_dom_pre_inst                      false
% 2.40/1.01  --qbf_sk_in                             false
% 2.40/1.01  --qbf_pred_elim                         true
% 2.40/1.01  --qbf_split                             512
% 2.40/1.01  
% 2.40/1.01  ------ BMC1 Options
% 2.40/1.01  
% 2.40/1.01  --bmc1_incremental                      false
% 2.40/1.01  --bmc1_axioms                           reachable_all
% 2.40/1.01  --bmc1_min_bound                        0
% 2.40/1.01  --bmc1_max_bound                        -1
% 2.40/1.01  --bmc1_max_bound_default                -1
% 2.40/1.01  --bmc1_symbol_reachability              true
% 2.40/1.01  --bmc1_property_lemmas                  false
% 2.40/1.01  --bmc1_k_induction                      false
% 2.40/1.01  --bmc1_non_equiv_states                 false
% 2.40/1.01  --bmc1_deadlock                         false
% 2.40/1.01  --bmc1_ucm                              false
% 2.40/1.01  --bmc1_add_unsat_core                   none
% 2.40/1.01  --bmc1_unsat_core_children              false
% 2.40/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/1.01  --bmc1_out_stat                         full
% 2.40/1.01  --bmc1_ground_init                      false
% 2.40/1.01  --bmc1_pre_inst_next_state              false
% 2.40/1.01  --bmc1_pre_inst_state                   false
% 2.40/1.01  --bmc1_pre_inst_reach_state             false
% 2.40/1.01  --bmc1_out_unsat_core                   false
% 2.40/1.01  --bmc1_aig_witness_out                  false
% 2.40/1.01  --bmc1_verbose                          false
% 2.40/1.01  --bmc1_dump_clauses_tptp                false
% 2.40/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.40/1.01  --bmc1_dump_file                        -
% 2.40/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.40/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.40/1.01  --bmc1_ucm_extend_mode                  1
% 2.40/1.01  --bmc1_ucm_init_mode                    2
% 2.40/1.01  --bmc1_ucm_cone_mode                    none
% 2.40/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.40/1.01  --bmc1_ucm_relax_model                  4
% 2.40/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.40/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/1.01  --bmc1_ucm_layered_model                none
% 2.40/1.01  --bmc1_ucm_max_lemma_size               10
% 2.40/1.01  
% 2.40/1.01  ------ AIG Options
% 2.40/1.01  
% 2.40/1.01  --aig_mode                              false
% 2.40/1.01  
% 2.40/1.01  ------ Instantiation Options
% 2.40/1.01  
% 2.40/1.01  --instantiation_flag                    true
% 2.40/1.01  --inst_sos_flag                         false
% 2.40/1.01  --inst_sos_phase                        true
% 2.40/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/1.01  --inst_lit_sel_side                     num_symb
% 2.40/1.01  --inst_solver_per_active                1400
% 2.40/1.01  --inst_solver_calls_frac                1.
% 2.40/1.01  --inst_passive_queue_type               priority_queues
% 2.40/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/1.01  --inst_passive_queues_freq              [25;2]
% 2.40/1.01  --inst_dismatching                      true
% 2.40/1.01  --inst_eager_unprocessed_to_passive     true
% 2.40/1.01  --inst_prop_sim_given                   true
% 2.40/1.01  --inst_prop_sim_new                     false
% 2.40/1.01  --inst_subs_new                         false
% 2.40/1.01  --inst_eq_res_simp                      false
% 2.40/1.01  --inst_subs_given                       false
% 2.40/1.01  --inst_orphan_elimination               true
% 2.40/1.01  --inst_learning_loop_flag               true
% 2.40/1.01  --inst_learning_start                   3000
% 2.40/1.01  --inst_learning_factor                  2
% 2.40/1.01  --inst_start_prop_sim_after_learn       3
% 2.40/1.01  --inst_sel_renew                        solver
% 2.40/1.01  --inst_lit_activity_flag                true
% 2.40/1.01  --inst_restr_to_given                   false
% 2.40/1.01  --inst_activity_threshold               500
% 2.40/1.01  --inst_out_proof                        true
% 2.40/1.01  
% 2.40/1.01  ------ Resolution Options
% 2.40/1.01  
% 2.40/1.01  --resolution_flag                       true
% 2.40/1.01  --res_lit_sel                           adaptive
% 2.40/1.01  --res_lit_sel_side                      none
% 2.40/1.01  --res_ordering                          kbo
% 2.40/1.01  --res_to_prop_solver                    active
% 2.40/1.01  --res_prop_simpl_new                    false
% 2.40/1.01  --res_prop_simpl_given                  true
% 2.40/1.01  --res_passive_queue_type                priority_queues
% 2.40/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/1.01  --res_passive_queues_freq               [15;5]
% 2.40/1.01  --res_forward_subs                      full
% 2.40/1.01  --res_backward_subs                     full
% 2.40/1.01  --res_forward_subs_resolution           true
% 2.40/1.01  --res_backward_subs_resolution          true
% 2.40/1.01  --res_orphan_elimination                true
% 2.40/1.01  --res_time_limit                        2.
% 2.40/1.01  --res_out_proof                         true
% 2.40/1.01  
% 2.40/1.01  ------ Superposition Options
% 2.40/1.01  
% 2.40/1.01  --superposition_flag                    true
% 2.40/1.01  --sup_passive_queue_type                priority_queues
% 2.40/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.40/1.01  --demod_completeness_check              fast
% 2.40/1.01  --demod_use_ground                      true
% 2.40/1.01  --sup_to_prop_solver                    passive
% 2.40/1.01  --sup_prop_simpl_new                    true
% 2.40/1.01  --sup_prop_simpl_given                  true
% 2.40/1.01  --sup_fun_splitting                     false
% 2.40/1.01  --sup_smt_interval                      50000
% 2.40/1.01  
% 2.40/1.01  ------ Superposition Simplification Setup
% 2.40/1.01  
% 2.40/1.01  --sup_indices_passive                   []
% 2.40/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.01  --sup_full_bw                           [BwDemod]
% 2.40/1.01  --sup_immed_triv                        [TrivRules]
% 2.40/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.01  --sup_immed_bw_main                     []
% 2.40/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.01  
% 2.40/1.01  ------ Combination Options
% 2.40/1.01  
% 2.40/1.01  --comb_res_mult                         3
% 2.40/1.01  --comb_sup_mult                         2
% 2.40/1.01  --comb_inst_mult                        10
% 2.40/1.01  
% 2.40/1.01  ------ Debug Options
% 2.40/1.01  
% 2.40/1.01  --dbg_backtrace                         false
% 2.40/1.01  --dbg_dump_prop_clauses                 false
% 2.40/1.01  --dbg_dump_prop_clauses_file            -
% 2.40/1.01  --dbg_out_stat                          false
% 2.40/1.01  ------ Parsing...
% 2.40/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.40/1.01  
% 2.40/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.40/1.01  
% 2.40/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.40/1.01  
% 2.40/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.40/1.01  ------ Proving...
% 2.40/1.01  ------ Problem Properties 
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  clauses                                 18
% 2.40/1.01  conjectures                             5
% 2.40/1.01  EPR                                     3
% 2.40/1.01  Horn                                    16
% 2.40/1.01  unary                                   5
% 2.40/1.01  binary                                  10
% 2.40/1.01  lits                                    35
% 2.40/1.01  lits eq                                 6
% 2.40/1.01  fd_pure                                 0
% 2.40/1.01  fd_pseudo                               0
% 2.40/1.01  fd_cond                                 0
% 2.40/1.01  fd_pseudo_cond                          0
% 2.40/1.01  AC symbols                              0
% 2.40/1.01  
% 2.40/1.01  ------ Schedule dynamic 5 is on 
% 2.40/1.01  
% 2.40/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  ------ 
% 2.40/1.01  Current options:
% 2.40/1.01  ------ 
% 2.40/1.01  
% 2.40/1.01  ------ Input Options
% 2.40/1.01  
% 2.40/1.01  --out_options                           all
% 2.40/1.01  --tptp_safe_out                         true
% 2.40/1.01  --problem_path                          ""
% 2.40/1.01  --include_path                          ""
% 2.40/1.01  --clausifier                            res/vclausify_rel
% 2.40/1.01  --clausifier_options                    --mode clausify
% 2.40/1.01  --stdin                                 false
% 2.40/1.01  --stats_out                             all
% 2.40/1.01  
% 2.40/1.01  ------ General Options
% 2.40/1.01  
% 2.40/1.01  --fof                                   false
% 2.40/1.01  --time_out_real                         305.
% 2.40/1.01  --time_out_virtual                      -1.
% 2.40/1.01  --symbol_type_check                     false
% 2.40/1.01  --clausify_out                          false
% 2.40/1.01  --sig_cnt_out                           false
% 2.40/1.01  --trig_cnt_out                          false
% 2.40/1.01  --trig_cnt_out_tolerance                1.
% 2.40/1.01  --trig_cnt_out_sk_spl                   false
% 2.40/1.01  --abstr_cl_out                          false
% 2.40/1.01  
% 2.40/1.01  ------ Global Options
% 2.40/1.01  
% 2.40/1.01  --schedule                              default
% 2.40/1.01  --add_important_lit                     false
% 2.40/1.01  --prop_solver_per_cl                    1000
% 2.40/1.01  --min_unsat_core                        false
% 2.40/1.01  --soft_assumptions                      false
% 2.40/1.01  --soft_lemma_size                       3
% 2.40/1.01  --prop_impl_unit_size                   0
% 2.40/1.01  --prop_impl_unit                        []
% 2.40/1.01  --share_sel_clauses                     true
% 2.40/1.01  --reset_solvers                         false
% 2.40/1.01  --bc_imp_inh                            [conj_cone]
% 2.40/1.01  --conj_cone_tolerance                   3.
% 2.40/1.01  --extra_neg_conj                        none
% 2.40/1.01  --large_theory_mode                     true
% 2.40/1.01  --prolific_symb_bound                   200
% 2.40/1.01  --lt_threshold                          2000
% 2.40/1.01  --clause_weak_htbl                      true
% 2.40/1.01  --gc_record_bc_elim                     false
% 2.40/1.01  
% 2.40/1.01  ------ Preprocessing Options
% 2.40/1.01  
% 2.40/1.01  --preprocessing_flag                    true
% 2.40/1.01  --time_out_prep_mult                    0.1
% 2.40/1.01  --splitting_mode                        input
% 2.40/1.01  --splitting_grd                         true
% 2.40/1.01  --splitting_cvd                         false
% 2.40/1.01  --splitting_cvd_svl                     false
% 2.40/1.01  --splitting_nvd                         32
% 2.40/1.01  --sub_typing                            true
% 2.40/1.01  --prep_gs_sim                           true
% 2.40/1.01  --prep_unflatten                        true
% 2.40/1.01  --prep_res_sim                          true
% 2.40/1.01  --prep_upred                            true
% 2.40/1.01  --prep_sem_filter                       exhaustive
% 2.40/1.01  --prep_sem_filter_out                   false
% 2.40/1.01  --pred_elim                             true
% 2.40/1.01  --res_sim_input                         true
% 2.40/1.01  --eq_ax_congr_red                       true
% 2.40/1.01  --pure_diseq_elim                       true
% 2.40/1.01  --brand_transform                       false
% 2.40/1.01  --non_eq_to_eq                          false
% 2.40/1.01  --prep_def_merge                        true
% 2.40/1.01  --prep_def_merge_prop_impl              false
% 2.40/1.01  --prep_def_merge_mbd                    true
% 2.40/1.01  --prep_def_merge_tr_red                 false
% 2.40/1.01  --prep_def_merge_tr_cl                  false
% 2.40/1.01  --smt_preprocessing                     true
% 2.40/1.01  --smt_ac_axioms                         fast
% 2.40/1.01  --preprocessed_out                      false
% 2.40/1.01  --preprocessed_stats                    false
% 2.40/1.01  
% 2.40/1.01  ------ Abstraction refinement Options
% 2.40/1.01  
% 2.40/1.01  --abstr_ref                             []
% 2.40/1.01  --abstr_ref_prep                        false
% 2.40/1.01  --abstr_ref_until_sat                   false
% 2.40/1.01  --abstr_ref_sig_restrict                funpre
% 2.40/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/1.01  --abstr_ref_under                       []
% 2.40/1.01  
% 2.40/1.01  ------ SAT Options
% 2.40/1.01  
% 2.40/1.01  --sat_mode                              false
% 2.40/1.01  --sat_fm_restart_options                ""
% 2.40/1.01  --sat_gr_def                            false
% 2.40/1.01  --sat_epr_types                         true
% 2.40/1.01  --sat_non_cyclic_types                  false
% 2.40/1.01  --sat_finite_models                     false
% 2.40/1.01  --sat_fm_lemmas                         false
% 2.40/1.01  --sat_fm_prep                           false
% 2.40/1.01  --sat_fm_uc_incr                        true
% 2.40/1.01  --sat_out_model                         small
% 2.40/1.01  --sat_out_clauses                       false
% 2.40/1.01  
% 2.40/1.01  ------ QBF Options
% 2.40/1.01  
% 2.40/1.01  --qbf_mode                              false
% 2.40/1.01  --qbf_elim_univ                         false
% 2.40/1.01  --qbf_dom_inst                          none
% 2.40/1.01  --qbf_dom_pre_inst                      false
% 2.40/1.01  --qbf_sk_in                             false
% 2.40/1.01  --qbf_pred_elim                         true
% 2.40/1.01  --qbf_split                             512
% 2.40/1.01  
% 2.40/1.01  ------ BMC1 Options
% 2.40/1.01  
% 2.40/1.01  --bmc1_incremental                      false
% 2.40/1.01  --bmc1_axioms                           reachable_all
% 2.40/1.01  --bmc1_min_bound                        0
% 2.40/1.01  --bmc1_max_bound                        -1
% 2.40/1.01  --bmc1_max_bound_default                -1
% 2.40/1.01  --bmc1_symbol_reachability              true
% 2.40/1.01  --bmc1_property_lemmas                  false
% 2.40/1.01  --bmc1_k_induction                      false
% 2.40/1.01  --bmc1_non_equiv_states                 false
% 2.40/1.01  --bmc1_deadlock                         false
% 2.40/1.01  --bmc1_ucm                              false
% 2.40/1.01  --bmc1_add_unsat_core                   none
% 2.40/1.01  --bmc1_unsat_core_children              false
% 2.40/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/1.01  --bmc1_out_stat                         full
% 2.40/1.01  --bmc1_ground_init                      false
% 2.40/1.01  --bmc1_pre_inst_next_state              false
% 2.40/1.01  --bmc1_pre_inst_state                   false
% 2.40/1.01  --bmc1_pre_inst_reach_state             false
% 2.40/1.01  --bmc1_out_unsat_core                   false
% 2.40/1.01  --bmc1_aig_witness_out                  false
% 2.40/1.01  --bmc1_verbose                          false
% 2.40/1.01  --bmc1_dump_clauses_tptp                false
% 2.40/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.40/1.01  --bmc1_dump_file                        -
% 2.40/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.40/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.40/1.01  --bmc1_ucm_extend_mode                  1
% 2.40/1.01  --bmc1_ucm_init_mode                    2
% 2.40/1.01  --bmc1_ucm_cone_mode                    none
% 2.40/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.40/1.01  --bmc1_ucm_relax_model                  4
% 2.40/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.40/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/1.01  --bmc1_ucm_layered_model                none
% 2.40/1.01  --bmc1_ucm_max_lemma_size               10
% 2.40/1.01  
% 2.40/1.01  ------ AIG Options
% 2.40/1.01  
% 2.40/1.01  --aig_mode                              false
% 2.40/1.01  
% 2.40/1.01  ------ Instantiation Options
% 2.40/1.01  
% 2.40/1.01  --instantiation_flag                    true
% 2.40/1.01  --inst_sos_flag                         false
% 2.40/1.01  --inst_sos_phase                        true
% 2.40/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/1.01  --inst_lit_sel_side                     none
% 2.40/1.01  --inst_solver_per_active                1400
% 2.40/1.01  --inst_solver_calls_frac                1.
% 2.40/1.01  --inst_passive_queue_type               priority_queues
% 2.40/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/1.01  --inst_passive_queues_freq              [25;2]
% 2.40/1.01  --inst_dismatching                      true
% 2.40/1.01  --inst_eager_unprocessed_to_passive     true
% 2.40/1.01  --inst_prop_sim_given                   true
% 2.40/1.01  --inst_prop_sim_new                     false
% 2.40/1.01  --inst_subs_new                         false
% 2.40/1.01  --inst_eq_res_simp                      false
% 2.40/1.01  --inst_subs_given                       false
% 2.40/1.01  --inst_orphan_elimination               true
% 2.40/1.01  --inst_learning_loop_flag               true
% 2.40/1.01  --inst_learning_start                   3000
% 2.40/1.01  --inst_learning_factor                  2
% 2.40/1.01  --inst_start_prop_sim_after_learn       3
% 2.40/1.01  --inst_sel_renew                        solver
% 2.40/1.01  --inst_lit_activity_flag                true
% 2.40/1.01  --inst_restr_to_given                   false
% 2.40/1.01  --inst_activity_threshold               500
% 2.40/1.01  --inst_out_proof                        true
% 2.40/1.01  
% 2.40/1.01  ------ Resolution Options
% 2.40/1.01  
% 2.40/1.01  --resolution_flag                       false
% 2.40/1.01  --res_lit_sel                           adaptive
% 2.40/1.01  --res_lit_sel_side                      none
% 2.40/1.01  --res_ordering                          kbo
% 2.40/1.01  --res_to_prop_solver                    active
% 2.40/1.01  --res_prop_simpl_new                    false
% 2.40/1.01  --res_prop_simpl_given                  true
% 2.40/1.01  --res_passive_queue_type                priority_queues
% 2.40/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/1.01  --res_passive_queues_freq               [15;5]
% 2.40/1.01  --res_forward_subs                      full
% 2.40/1.01  --res_backward_subs                     full
% 2.40/1.01  --res_forward_subs_resolution           true
% 2.40/1.01  --res_backward_subs_resolution          true
% 2.40/1.01  --res_orphan_elimination                true
% 2.40/1.01  --res_time_limit                        2.
% 2.40/1.01  --res_out_proof                         true
% 2.40/1.01  
% 2.40/1.01  ------ Superposition Options
% 2.40/1.01  
% 2.40/1.01  --superposition_flag                    true
% 2.40/1.01  --sup_passive_queue_type                priority_queues
% 2.40/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.40/1.01  --demod_completeness_check              fast
% 2.40/1.01  --demod_use_ground                      true
% 2.40/1.01  --sup_to_prop_solver                    passive
% 2.40/1.01  --sup_prop_simpl_new                    true
% 2.40/1.01  --sup_prop_simpl_given                  true
% 2.40/1.01  --sup_fun_splitting                     false
% 2.40/1.01  --sup_smt_interval                      50000
% 2.40/1.01  
% 2.40/1.01  ------ Superposition Simplification Setup
% 2.40/1.01  
% 2.40/1.01  --sup_indices_passive                   []
% 2.40/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.01  --sup_full_bw                           [BwDemod]
% 2.40/1.01  --sup_immed_triv                        [TrivRules]
% 2.40/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.01  --sup_immed_bw_main                     []
% 2.40/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.01  
% 2.40/1.01  ------ Combination Options
% 2.40/1.01  
% 2.40/1.01  --comb_res_mult                         3
% 2.40/1.01  --comb_sup_mult                         2
% 2.40/1.01  --comb_inst_mult                        10
% 2.40/1.01  
% 2.40/1.01  ------ Debug Options
% 2.40/1.01  
% 2.40/1.01  --dbg_backtrace                         false
% 2.40/1.01  --dbg_dump_prop_clauses                 false
% 2.40/1.01  --dbg_dump_prop_clauses_file            -
% 2.40/1.01  --dbg_out_stat                          false
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  ------ Proving...
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  % SZS status Theorem for theBenchmark.p
% 2.40/1.01  
% 2.40/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.40/1.01  
% 2.40/1.01  fof(f12,conjecture,(
% 2.40/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 2.40/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f13,negated_conjecture,(
% 2.40/1.01    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 2.40/1.01    inference(negated_conjecture,[],[f12])).
% 2.40/1.01  
% 2.40/1.01  fof(f28,plain,(
% 2.40/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.40/1.01    inference(ennf_transformation,[],[f13])).
% 2.40/1.01  
% 2.40/1.01  fof(f29,plain,(
% 2.40/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.40/1.01    inference(flattening,[],[f28])).
% 2.40/1.01  
% 2.40/1.01  fof(f31,plain,(
% 2.40/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.40/1.01    inference(nnf_transformation,[],[f29])).
% 2.40/1.01  
% 2.40/1.01  fof(f32,plain,(
% 2.40/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.40/1.01    inference(flattening,[],[f31])).
% 2.40/1.01  
% 2.40/1.01  fof(f37,plain,(
% 2.40/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) => ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,sK4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),sK4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,sK4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(X1)))) )),
% 2.40/1.01    introduced(choice_axiom,[])).
% 2.40/1.01  
% 2.40/1.01  fof(f36,plain,(
% 2.40/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : ((~r1_tarski(sK3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,sK3),X4)) & (r1_tarski(sK3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,sK3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 2.40/1.01    introduced(choice_axiom,[])).
% 2.40/1.01  
% 2.40/1.01  fof(f35,plain,(
% 2.40/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,sK2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,sK2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,sK2,X4)) | r1_tarski(k7_relset_1(X0,X1,sK2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK2,X0,X1) & v1_funct_1(sK2))) )),
% 2.40/1.01    introduced(choice_axiom,[])).
% 2.40/1.01  
% 2.40/1.01  fof(f34,plain,(
% 2.40/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,sK1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,sK1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,sK1,X2,X4)) | r1_tarski(k7_relset_1(X0,sK1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) & v1_funct_2(X2,X0,sK1) & v1_funct_1(X2)) & ~v1_xboole_0(sK1))) )),
% 2.40/1.01    introduced(choice_axiom,[])).
% 2.40/1.01  
% 2.40/1.01  fof(f33,plain,(
% 2.40/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 2.40/1.01    introduced(choice_axiom,[])).
% 2.40/1.01  
% 2.40/1.01  fof(f38,plain,(
% 2.40/1.01    (((((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 2.40/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f32,f37,f36,f35,f34,f33])).
% 2.40/1.01  
% 2.40/1.01  fof(f56,plain,(
% 2.40/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.40/1.01    inference(cnf_transformation,[],[f38])).
% 2.40/1.01  
% 2.40/1.01  fof(f9,axiom,(
% 2.40/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.40/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f24,plain,(
% 2.40/1.01    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/1.01    inference(ennf_transformation,[],[f9])).
% 2.40/1.01  
% 2.40/1.01  fof(f48,plain,(
% 2.40/1.01    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.40/1.01    inference(cnf_transformation,[],[f24])).
% 2.40/1.01  
% 2.40/1.01  fof(f59,plain,(
% 2.40/1.01    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 2.40/1.01    inference(cnf_transformation,[],[f38])).
% 2.40/1.01  
% 2.40/1.01  fof(f10,axiom,(
% 2.40/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.40/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f25,plain,(
% 2.40/1.01    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/1.01    inference(ennf_transformation,[],[f10])).
% 2.40/1.01  
% 2.40/1.01  fof(f49,plain,(
% 2.40/1.01    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.40/1.01    inference(cnf_transformation,[],[f25])).
% 2.40/1.01  
% 2.40/1.01  fof(f2,axiom,(
% 2.40/1.01    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.40/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f14,plain,(
% 2.40/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.40/1.01    inference(ennf_transformation,[],[f2])).
% 2.40/1.01  
% 2.40/1.01  fof(f15,plain,(
% 2.40/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.40/1.01    inference(flattening,[],[f14])).
% 2.40/1.01  
% 2.40/1.01  fof(f40,plain,(
% 2.40/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f15])).
% 2.40/1.01  
% 2.40/1.01  fof(f8,axiom,(
% 2.40/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.40/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f23,plain,(
% 2.40/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/1.01    inference(ennf_transformation,[],[f8])).
% 2.40/1.01  
% 2.40/1.01  fof(f47,plain,(
% 2.40/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.40/1.01    inference(cnf_transformation,[],[f23])).
% 2.40/1.01  
% 2.40/1.01  fof(f7,axiom,(
% 2.40/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 2.40/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f21,plain,(
% 2.40/1.01    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.40/1.01    inference(ennf_transformation,[],[f7])).
% 2.40/1.01  
% 2.40/1.01  fof(f22,plain,(
% 2.40/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.40/1.01    inference(flattening,[],[f21])).
% 2.40/1.01  
% 2.40/1.01  fof(f46,plain,(
% 2.40/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f22])).
% 2.40/1.01  
% 2.40/1.01  fof(f54,plain,(
% 2.40/1.01    v1_funct_1(sK2)),
% 2.40/1.01    inference(cnf_transformation,[],[f38])).
% 2.40/1.01  
% 2.40/1.01  fof(f11,axiom,(
% 2.40/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 2.40/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f26,plain,(
% 2.40/1.01    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.40/1.01    inference(ennf_transformation,[],[f11])).
% 2.40/1.01  
% 2.40/1.01  fof(f27,plain,(
% 2.40/1.01    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.40/1.01    inference(flattening,[],[f26])).
% 2.40/1.01  
% 2.40/1.01  fof(f50,plain,(
% 2.40/1.01    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f27])).
% 2.40/1.01  
% 2.40/1.01  fof(f55,plain,(
% 2.40/1.01    v1_funct_2(sK2,sK0,sK1)),
% 2.40/1.01    inference(cnf_transformation,[],[f38])).
% 2.40/1.01  
% 2.40/1.01  fof(f1,axiom,(
% 2.40/1.01    v1_xboole_0(k1_xboole_0)),
% 2.40/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f39,plain,(
% 2.40/1.01    v1_xboole_0(k1_xboole_0)),
% 2.40/1.01    inference(cnf_transformation,[],[f1])).
% 2.40/1.01  
% 2.40/1.01  fof(f53,plain,(
% 2.40/1.01    ~v1_xboole_0(sK1)),
% 2.40/1.01    inference(cnf_transformation,[],[f38])).
% 2.40/1.01  
% 2.40/1.01  fof(f5,axiom,(
% 2.40/1.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.40/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f18,plain,(
% 2.40/1.01    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.40/1.01    inference(ennf_transformation,[],[f5])).
% 2.40/1.01  
% 2.40/1.01  fof(f44,plain,(
% 2.40/1.01    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f18])).
% 2.40/1.01  
% 2.40/1.01  fof(f6,axiom,(
% 2.40/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 2.40/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f19,plain,(
% 2.40/1.01    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.40/1.01    inference(ennf_transformation,[],[f6])).
% 2.40/1.01  
% 2.40/1.01  fof(f20,plain,(
% 2.40/1.01    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.40/1.01    inference(flattening,[],[f19])).
% 2.40/1.01  
% 2.40/1.01  fof(f45,plain,(
% 2.40/1.01    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f20])).
% 2.40/1.01  
% 2.40/1.01  fof(f57,plain,(
% 2.40/1.01    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 2.40/1.01    inference(cnf_transformation,[],[f38])).
% 2.40/1.01  
% 2.40/1.01  fof(f3,axiom,(
% 2.40/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.40/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f30,plain,(
% 2.40/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.40/1.01    inference(nnf_transformation,[],[f3])).
% 2.40/1.01  
% 2.40/1.01  fof(f41,plain,(
% 2.40/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.40/1.01    inference(cnf_transformation,[],[f30])).
% 2.40/1.01  
% 2.40/1.01  fof(f4,axiom,(
% 2.40/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.40/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f16,plain,(
% 2.40/1.01    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 2.40/1.01    inference(ennf_transformation,[],[f4])).
% 2.40/1.01  
% 2.40/1.01  fof(f17,plain,(
% 2.40/1.01    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 2.40/1.01    inference(flattening,[],[f16])).
% 2.40/1.01  
% 2.40/1.01  fof(f43,plain,(
% 2.40/1.01    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f17])).
% 2.40/1.01  
% 2.40/1.01  fof(f60,plain,(
% 2.40/1.01    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 2.40/1.01    inference(cnf_transformation,[],[f38])).
% 2.40/1.01  
% 2.40/1.01  cnf(c_17,negated_conjecture,
% 2.40/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.40/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1454,negated_conjecture,
% 2.40/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.40/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1908,plain,
% 2.40/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_1454]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_9,plain,
% 2.40/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/1.01      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.40/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1460,plain,
% 2.40/1.01      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 2.40/1.01      | k7_relset_1(X1_47,X2_47,X0_47,X3_47) = k9_relat_1(X0_47,X3_47) ),
% 2.40/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1902,plain,
% 2.40/1.01      ( k7_relset_1(X0_47,X1_47,X2_47,X3_47) = k9_relat_1(X2_47,X3_47)
% 2.40/1.01      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_1460]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2778,plain,
% 2.40/1.01      ( k7_relset_1(sK0,sK1,sK2,X0_47) = k9_relat_1(sK2,X0_47) ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_1908,c_1902]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_14,negated_conjecture,
% 2.40/1.01      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
% 2.40/1.01      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
% 2.40/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1457,negated_conjecture,
% 2.40/1.01      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
% 2.40/1.01      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
% 2.40/1.01      inference(subtyping,[status(esa)],[c_14]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1905,plain,
% 2.40/1.01      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
% 2.40/1.01      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) = iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_1457]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2855,plain,
% 2.40/1.01      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
% 2.40/1.01      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) = iProver_top ),
% 2.40/1.01      inference(demodulation,[status(thm)],[c_2778,c_1905]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_10,plain,
% 2.40/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/1.01      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.40/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1459,plain,
% 2.40/1.01      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 2.40/1.01      | k8_relset_1(X1_47,X2_47,X0_47,X3_47) = k10_relat_1(X0_47,X3_47) ),
% 2.40/1.01      inference(subtyping,[status(esa)],[c_10]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1903,plain,
% 2.40/1.01      ( k8_relset_1(X0_47,X1_47,X2_47,X3_47) = k10_relat_1(X2_47,X3_47)
% 2.40/1.01      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_1459]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2841,plain,
% 2.40/1.01      ( k8_relset_1(sK0,sK1,sK2,X0_47) = k10_relat_1(sK2,X0_47) ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_1908,c_1903]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_3123,plain,
% 2.40/1.01      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
% 2.40/1.01      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
% 2.40/1.01      inference(demodulation,[status(thm)],[c_2855,c_2841]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1,plain,
% 2.40/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 2.40/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1466,plain,
% 2.40/1.01      ( ~ r1_tarski(X0_47,X1_47)
% 2.40/1.01      | ~ r1_tarski(X2_47,X0_47)
% 2.40/1.01      | r1_tarski(X2_47,X1_47) ),
% 2.40/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1896,plain,
% 2.40/1.01      ( r1_tarski(X0_47,X1_47) != iProver_top
% 2.40/1.01      | r1_tarski(X2_47,X0_47) != iProver_top
% 2.40/1.01      | r1_tarski(X2_47,X1_47) = iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_1466]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_3128,plain,
% 2.40/1.01      ( r1_tarski(X0_47,k9_relat_1(sK2,sK3)) != iProver_top
% 2.40/1.01      | r1_tarski(X0_47,sK4) = iProver_top
% 2.40/1.01      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_3123,c_1896]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_26,plain,
% 2.40/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_8,plain,
% 2.40/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/1.01      | v1_relat_1(X0) ),
% 2.40/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1461,plain,
% 2.40/1.01      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 2.40/1.01      | v1_relat_1(X0_47) ),
% 2.40/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2016,plain,
% 2.40/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.40/1.01      | v1_relat_1(sK2) ),
% 2.40/1.01      inference(instantiation,[status(thm)],[c_1461]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2017,plain,
% 2.40/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.40/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_2016]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_7,plain,
% 2.40/1.01      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 2.40/1.01      | ~ r1_tarski(X0,k1_relat_1(X1))
% 2.40/1.01      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 2.40/1.01      | ~ v1_funct_1(X1)
% 2.40/1.01      | ~ v1_relat_1(X1) ),
% 2.40/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_19,negated_conjecture,
% 2.40/1.01      ( v1_funct_1(sK2) ),
% 2.40/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_336,plain,
% 2.40/1.01      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 2.40/1.01      | ~ r1_tarski(X0,k1_relat_1(X1))
% 2.40/1.01      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 2.40/1.01      | ~ v1_relat_1(X1)
% 2.40/1.01      | sK2 != X1 ),
% 2.40/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_337,plain,
% 2.40/1.01      ( r1_tarski(X0,k10_relat_1(sK2,X1))
% 2.40/1.01      | ~ r1_tarski(X0,k1_relat_1(sK2))
% 2.40/1.01      | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
% 2.40/1.01      | ~ v1_relat_1(sK2) ),
% 2.40/1.01      inference(unflattening,[status(thm)],[c_336]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1449,plain,
% 2.40/1.01      ( r1_tarski(X0_47,k10_relat_1(sK2,X1_47))
% 2.40/1.01      | ~ r1_tarski(X0_47,k1_relat_1(sK2))
% 2.40/1.01      | ~ r1_tarski(k9_relat_1(sK2,X0_47),X1_47)
% 2.40/1.01      | ~ v1_relat_1(sK2) ),
% 2.40/1.01      inference(subtyping,[status(esa)],[c_337]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1910,plain,
% 2.40/1.01      ( r1_tarski(X0_47,k10_relat_1(sK2,X1_47)) = iProver_top
% 2.40/1.01      | r1_tarski(X0_47,k1_relat_1(sK2)) != iProver_top
% 2.40/1.01      | r1_tarski(k9_relat_1(sK2,X0_47),X1_47) != iProver_top
% 2.40/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_1449]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1512,plain,
% 2.40/1.01      ( r1_tarski(X0_47,k10_relat_1(sK2,X1_47)) = iProver_top
% 2.40/1.01      | r1_tarski(X0_47,k1_relat_1(sK2)) != iProver_top
% 2.40/1.01      | r1_tarski(k9_relat_1(sK2,X0_47),X1_47) != iProver_top
% 2.40/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_1449]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2713,plain,
% 2.40/1.01      ( r1_tarski(k9_relat_1(sK2,X0_47),X1_47) != iProver_top
% 2.40/1.01      | r1_tarski(X0_47,k1_relat_1(sK2)) != iProver_top
% 2.40/1.01      | r1_tarski(X0_47,k10_relat_1(sK2,X1_47)) = iProver_top ),
% 2.40/1.01      inference(global_propositional_subsumption,
% 2.40/1.01                [status(thm)],
% 2.40/1.01                [c_1910,c_26,c_1512,c_2017]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2714,plain,
% 2.40/1.01      ( r1_tarski(X0_47,k10_relat_1(sK2,X1_47)) = iProver_top
% 2.40/1.01      | r1_tarski(X0_47,k1_relat_1(sK2)) != iProver_top
% 2.40/1.01      | r1_tarski(k9_relat_1(sK2,X0_47),X1_47) != iProver_top ),
% 2.40/1.01      inference(renaming,[status(thm)],[c_2713]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_3127,plain,
% 2.40/1.01      ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top
% 2.40/1.01      | r1_tarski(sK3,k1_relat_1(sK2)) != iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_3123,c_2714]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_12,plain,
% 2.40/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.40/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/1.01      | ~ v1_funct_1(X0)
% 2.40/1.01      | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = X1
% 2.40/1.01      | k1_xboole_0 = X2 ),
% 2.40/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_18,negated_conjecture,
% 2.40/1.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.40/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_310,plain,
% 2.40/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/1.01      | ~ v1_funct_1(X0)
% 2.40/1.01      | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = X1
% 2.40/1.01      | sK2 != X0
% 2.40/1.01      | sK1 != X2
% 2.40/1.01      | sK0 != X1
% 2.40/1.01      | k1_xboole_0 = X2 ),
% 2.40/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_311,plain,
% 2.40/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.40/1.01      | ~ v1_funct_1(sK2)
% 2.40/1.01      | k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) = sK0
% 2.40/1.01      | k1_xboole_0 = sK1 ),
% 2.40/1.01      inference(unflattening,[status(thm)],[c_310]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_313,plain,
% 2.40/1.01      ( k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) = sK0
% 2.40/1.01      | k1_xboole_0 = sK1 ),
% 2.40/1.01      inference(global_propositional_subsumption,
% 2.40/1.01                [status(thm)],
% 2.40/1.01                [c_311,c_19,c_17]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1451,plain,
% 2.40/1.01      ( k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) = sK0
% 2.40/1.01      | k1_xboole_0 = sK1 ),
% 2.40/1.01      inference(subtyping,[status(esa)],[c_313]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2857,plain,
% 2.40/1.01      ( k8_relset_1(sK0,sK1,sK2,k9_relat_1(sK2,sK0)) = sK0
% 2.40/1.01      | sK1 = k1_xboole_0 ),
% 2.40/1.01      inference(demodulation,[status(thm)],[c_2778,c_1451]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_0,plain,
% 2.40/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.40/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_20,negated_conjecture,
% 2.40/1.01      ( ~ v1_xboole_0(sK1) ),
% 2.40/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_809,plain,
% 2.40/1.01      ( sK1 != k1_xboole_0 ),
% 2.40/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1453,plain,
% 2.40/1.01      ( sK1 != k1_xboole_0 ),
% 2.40/1.01      inference(subtyping,[status(esa)],[c_809]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_3117,plain,
% 2.40/1.01      ( k8_relset_1(sK0,sK1,sK2,k9_relat_1(sK2,sK0)) = sK0 ),
% 2.40/1.01      inference(global_propositional_subsumption,
% 2.40/1.01                [status(thm)],
% 2.40/1.01                [c_2857,c_1453]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_3120,plain,
% 2.40/1.01      ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_2841,c_3117]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_5,plain,
% 2.40/1.01      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.40/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1462,plain,
% 2.40/1.01      ( r1_tarski(k10_relat_1(X0_47,X1_47),k1_relat_1(X0_47))
% 2.40/1.01      | ~ v1_relat_1(X0_47) ),
% 2.40/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1900,plain,
% 2.40/1.01      ( r1_tarski(k10_relat_1(X0_47,X1_47),k1_relat_1(X0_47)) = iProver_top
% 2.40/1.01      | v1_relat_1(X0_47) != iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_1462]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_3235,plain,
% 2.40/1.01      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
% 2.40/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_3120,c_1900]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_6,plain,
% 2.40/1.01      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 2.40/1.01      | ~ v1_funct_1(X0)
% 2.40/1.01      | ~ v1_relat_1(X0) ),
% 2.40/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_324,plain,
% 2.40/1.01      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 2.40/1.01      | ~ v1_relat_1(X0)
% 2.40/1.01      | sK2 != X0 ),
% 2.40/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_19]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_325,plain,
% 2.40/1.01      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
% 2.40/1.01      | ~ v1_relat_1(sK2) ),
% 2.40/1.01      inference(unflattening,[status(thm)],[c_324]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1450,plain,
% 2.40/1.01      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_47)),X0_47)
% 2.40/1.01      | ~ v1_relat_1(sK2) ),
% 2.40/1.01      inference(subtyping,[status(esa)],[c_325]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1909,plain,
% 2.40/1.01      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_47)),X0_47) = iProver_top
% 2.40/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_1450]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1511,plain,
% 2.40/1.01      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_47)),X0_47) = iProver_top
% 2.40/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_1450]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2629,plain,
% 2.40/1.01      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_47)),X0_47) = iProver_top ),
% 2.40/1.01      inference(global_propositional_subsumption,
% 2.40/1.01                [status(thm)],
% 2.40/1.01                [c_1909,c_26,c_1511,c_2017]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_3234,plain,
% 2.40/1.01      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0)) = iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_3120,c_2629]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_3246,plain,
% 2.40/1.01      ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) = iProver_top
% 2.40/1.01      | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_3234,c_2714]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_3250,plain,
% 2.40/1.01      ( r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top
% 2.40/1.01      | r1_tarski(sK0,sK0) = iProver_top ),
% 2.40/1.01      inference(light_normalisation,[status(thm)],[c_3246,c_3120]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_16,negated_conjecture,
% 2.40/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 2.40/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1455,negated_conjecture,
% 2.40/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 2.40/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1907,plain,
% 2.40/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_1455]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_3,plain,
% 2.40/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.40/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1464,plain,
% 2.40/1.01      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
% 2.40/1.01      | r1_tarski(X0_47,X1_47) ),
% 2.40/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1898,plain,
% 2.40/1.01      ( m1_subset_1(X0_47,k1_zfmisc_1(X1_47)) != iProver_top
% 2.40/1.01      | r1_tarski(X0_47,X1_47) = iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_1464]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2274,plain,
% 2.40/1.01      ( r1_tarski(sK3,sK0) = iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_1907,c_1898]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_3553,plain,
% 2.40/1.01      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 2.40/1.01      inference(global_propositional_subsumption,
% 2.40/1.01                [status(thm)],
% 2.40/1.01                [c_3235,c_26,c_2017]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_3558,plain,
% 2.40/1.01      ( r1_tarski(X0_47,k1_relat_1(sK2)) = iProver_top
% 2.40/1.01      | r1_tarski(X0_47,sK0) != iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_3553,c_1896]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_3644,plain,
% 2.40/1.01      ( r1_tarski(X0_47,X1_47) != iProver_top
% 2.40/1.01      | r1_tarski(X0_47,k1_relat_1(sK2)) = iProver_top
% 2.40/1.01      | r1_tarski(X1_47,sK0) != iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_3558,c_1896]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_5792,plain,
% 2.40/1.01      ( r1_tarski(sK0,sK0) != iProver_top
% 2.40/1.01      | r1_tarski(sK3,k1_relat_1(sK2)) = iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_2274,c_3644]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_6218,plain,
% 2.40/1.01      ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
% 2.40/1.01      inference(global_propositional_subsumption,
% 2.40/1.01                [status(thm)],
% 2.40/1.01                [c_3128,c_26,c_2017,c_3127,c_3235,c_3250,c_5792]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_4,plain,
% 2.40/1.01      ( ~ r1_tarski(X0,X1)
% 2.40/1.01      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 2.40/1.01      | ~ v1_relat_1(X2) ),
% 2.40/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1463,plain,
% 2.40/1.01      ( ~ r1_tarski(X0_47,X1_47)
% 2.40/1.01      | r1_tarski(k9_relat_1(X2_47,X0_47),k9_relat_1(X2_47,X1_47))
% 2.40/1.01      | ~ v1_relat_1(X2_47) ),
% 2.40/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1899,plain,
% 2.40/1.01      ( r1_tarski(X0_47,X1_47) != iProver_top
% 2.40/1.01      | r1_tarski(k9_relat_1(X2_47,X0_47),k9_relat_1(X2_47,X1_47)) = iProver_top
% 2.40/1.01      | v1_relat_1(X2_47) != iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_1463]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2636,plain,
% 2.40/1.01      ( r1_tarski(X0_47,X1_47) = iProver_top
% 2.40/1.01      | r1_tarski(X0_47,k9_relat_1(sK2,k10_relat_1(sK2,X1_47))) != iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_2629,c_1896]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_3857,plain,
% 2.40/1.01      ( r1_tarski(X0_47,k10_relat_1(sK2,X1_47)) != iProver_top
% 2.40/1.01      | r1_tarski(k9_relat_1(sK2,X0_47),X1_47) = iProver_top
% 2.40/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_1899,c_2636]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_9689,plain,
% 2.40/1.01      ( r1_tarski(k9_relat_1(sK2,X0_47),X1_47) = iProver_top
% 2.40/1.01      | r1_tarski(X0_47,k10_relat_1(sK2,X1_47)) != iProver_top ),
% 2.40/1.01      inference(global_propositional_subsumption,
% 2.40/1.01                [status(thm)],
% 2.40/1.01                [c_3857,c_26,c_2017]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_9690,plain,
% 2.40/1.01      ( r1_tarski(X0_47,k10_relat_1(sK2,X1_47)) != iProver_top
% 2.40/1.01      | r1_tarski(k9_relat_1(sK2,X0_47),X1_47) = iProver_top ),
% 2.40/1.01      inference(renaming,[status(thm)],[c_9689]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_9701,plain,
% 2.40/1.01      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_6218,c_9690]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_13,negated_conjecture,
% 2.40/1.01      ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
% 2.40/1.01      | ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
% 2.40/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1458,negated_conjecture,
% 2.40/1.01      ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
% 2.40/1.01      | ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
% 2.40/1.01      inference(subtyping,[status(esa)],[c_13]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1904,plain,
% 2.40/1.01      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
% 2.40/1.01      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) != iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_1458]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2856,plain,
% 2.40/1.01      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top
% 2.40/1.01      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) != iProver_top ),
% 2.40/1.01      inference(demodulation,[status(thm)],[c_2778,c_1904]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_3059,plain,
% 2.40/1.01      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top
% 2.40/1.01      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
% 2.40/1.01      inference(demodulation,[status(thm)],[c_2856,c_2841]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(contradiction,plain,
% 2.40/1.01      ( $false ),
% 2.40/1.01      inference(minisat,
% 2.40/1.01                [status(thm)],
% 2.40/1.01                [c_9701,c_5792,c_3250,c_3235,c_3127,c_3059,c_2017,c_26]) ).
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.40/1.01  
% 2.40/1.01  ------                               Statistics
% 2.40/1.01  
% 2.40/1.01  ------ General
% 2.40/1.01  
% 2.40/1.01  abstr_ref_over_cycles:                  0
% 2.40/1.01  abstr_ref_under_cycles:                 0
% 2.40/1.01  gc_basic_clause_elim:                   0
% 2.40/1.01  forced_gc_time:                         0
% 2.40/1.01  parsing_time:                           0.016
% 2.40/1.01  unif_index_cands_time:                  0.
% 2.40/1.01  unif_index_add_time:                    0.
% 2.40/1.01  orderings_time:                         0.
% 2.40/1.01  out_proof_time:                         0.01
% 2.40/1.01  total_time:                             0.273
% 2.40/1.01  num_of_symbols:                         52
% 2.40/1.01  num_of_terms:                           8711
% 2.40/1.01  
% 2.40/1.01  ------ Preprocessing
% 2.40/1.01  
% 2.40/1.01  num_of_splits:                          0
% 2.40/1.01  num_of_split_atoms:                     0
% 2.40/1.01  num_of_reused_defs:                     0
% 2.40/1.01  num_eq_ax_congr_red:                    8
% 2.40/1.01  num_of_sem_filtered_clauses:            1
% 2.40/1.01  num_of_subtypes:                        2
% 2.40/1.01  monotx_restored_types:                  0
% 2.40/1.01  sat_num_of_epr_types:                   0
% 2.40/1.01  sat_num_of_non_cyclic_types:            0
% 2.40/1.01  sat_guarded_non_collapsed_types:        0
% 2.40/1.01  num_pure_diseq_elim:                    0
% 2.40/1.01  simp_replaced_by:                       0
% 2.40/1.01  res_preprocessed:                       123
% 2.40/1.01  prep_upred:                             0
% 2.40/1.01  prep_unflattend:                        61
% 2.40/1.01  smt_new_axioms:                         0
% 2.40/1.01  pred_elim_cands:                        3
% 2.40/1.01  pred_elim:                              3
% 2.40/1.01  pred_elim_cl:                           4
% 2.40/1.01  pred_elim_cycles:                       10
% 2.40/1.01  merged_defs:                            20
% 2.40/1.01  merged_defs_ncl:                        0
% 2.40/1.01  bin_hyper_res:                          20
% 2.40/1.01  prep_cycles:                            5
% 2.40/1.01  pred_elim_time:                         0.012
% 2.40/1.01  splitting_time:                         0.
% 2.40/1.01  sem_filter_time:                        0.
% 2.40/1.01  monotx_time:                            0.
% 2.40/1.01  subtype_inf_time:                       0.
% 2.40/1.01  
% 2.40/1.01  ------ Problem properties
% 2.40/1.01  
% 2.40/1.01  clauses:                                18
% 2.40/1.01  conjectures:                            5
% 2.40/1.01  epr:                                    3
% 2.40/1.01  horn:                                   16
% 2.40/1.01  ground:                                 8
% 2.40/1.01  unary:                                  5
% 2.40/1.01  binary:                                 10
% 2.40/1.01  lits:                                   35
% 2.40/1.01  lits_eq:                                6
% 2.40/1.01  fd_pure:                                0
% 2.40/1.01  fd_pseudo:                              0
% 2.40/1.01  fd_cond:                                0
% 2.40/1.01  fd_pseudo_cond:                         0
% 2.40/1.01  ac_symbols:                             0
% 2.40/1.01  
% 2.40/1.01  ------ Propositional Solver
% 2.40/1.01  
% 2.40/1.01  prop_solver_calls:                      31
% 2.40/1.01  prop_fast_solver_calls:                 938
% 2.40/1.01  smt_solver_calls:                       0
% 2.40/1.01  smt_fast_solver_calls:                  0
% 2.40/1.01  prop_num_of_clauses:                    3626
% 2.40/1.01  prop_preprocess_simplified:             7088
% 2.40/1.01  prop_fo_subsumed:                       23
% 2.40/1.01  prop_solver_time:                       0.
% 2.40/1.01  smt_solver_time:                        0.
% 2.40/1.01  smt_fast_solver_time:                   0.
% 2.40/1.01  prop_fast_solver_time:                  0.
% 2.40/1.01  prop_unsat_core_time:                   0.
% 2.40/1.01  
% 2.40/1.01  ------ QBF
% 2.40/1.01  
% 2.40/1.01  qbf_q_res:                              0
% 2.40/1.01  qbf_num_tautologies:                    0
% 2.40/1.01  qbf_prep_cycles:                        0
% 2.40/1.01  
% 2.40/1.01  ------ BMC1
% 2.40/1.01  
% 2.40/1.01  bmc1_current_bound:                     -1
% 2.40/1.01  bmc1_last_solved_bound:                 -1
% 2.40/1.01  bmc1_unsat_core_size:                   -1
% 2.40/1.01  bmc1_unsat_core_parents_size:           -1
% 2.40/1.01  bmc1_merge_next_fun:                    0
% 2.40/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.40/1.01  
% 2.40/1.01  ------ Instantiation
% 2.40/1.01  
% 2.40/1.01  inst_num_of_clauses:                    865
% 2.40/1.01  inst_num_in_passive:                    166
% 2.40/1.01  inst_num_in_active:                     404
% 2.40/1.01  inst_num_in_unprocessed:                295
% 2.40/1.01  inst_num_of_loops:                      490
% 2.40/1.01  inst_num_of_learning_restarts:          0
% 2.40/1.01  inst_num_moves_active_passive:          83
% 2.40/1.01  inst_lit_activity:                      0
% 2.40/1.01  inst_lit_activity_moves:                0
% 2.40/1.01  inst_num_tautologies:                   0
% 2.40/1.01  inst_num_prop_implied:                  0
% 2.40/1.01  inst_num_existing_simplified:           0
% 2.40/1.01  inst_num_eq_res_simplified:             0
% 2.40/1.01  inst_num_child_elim:                    0
% 2.40/1.01  inst_num_of_dismatching_blockings:      355
% 2.40/1.01  inst_num_of_non_proper_insts:           577
% 2.40/1.01  inst_num_of_duplicates:                 0
% 2.40/1.01  inst_inst_num_from_inst_to_res:         0
% 2.40/1.01  inst_dismatching_checking_time:         0.
% 2.40/1.01  
% 2.40/1.01  ------ Resolution
% 2.40/1.01  
% 2.40/1.01  res_num_of_clauses:                     0
% 2.40/1.01  res_num_in_passive:                     0
% 2.40/1.01  res_num_in_active:                      0
% 2.40/1.01  res_num_of_loops:                       128
% 2.40/1.01  res_forward_subset_subsumed:            36
% 2.40/1.01  res_backward_subset_subsumed:           0
% 2.40/1.01  res_forward_subsumed:                   0
% 2.40/1.01  res_backward_subsumed:                  0
% 2.40/1.01  res_forward_subsumption_resolution:     0
% 2.40/1.01  res_backward_subsumption_resolution:    0
% 2.40/1.01  res_clause_to_clause_subsumption:       1482
% 2.40/1.01  res_orphan_elimination:                 0
% 2.40/1.01  res_tautology_del:                      99
% 2.40/1.01  res_num_eq_res_simplified:              0
% 2.40/1.01  res_num_sel_changes:                    0
% 2.40/1.01  res_moves_from_active_to_pass:          0
% 2.40/1.01  
% 2.40/1.01  ------ Superposition
% 2.40/1.01  
% 2.40/1.01  sup_time_total:                         0.
% 2.40/1.01  sup_time_generating:                    0.
% 2.40/1.01  sup_time_sim_full:                      0.
% 2.40/1.01  sup_time_sim_immed:                     0.
% 2.40/1.01  
% 2.40/1.01  sup_num_of_clauses:                     288
% 2.40/1.01  sup_num_in_active:                      92
% 2.40/1.01  sup_num_in_passive:                     196
% 2.40/1.01  sup_num_of_loops:                       97
% 2.40/1.01  sup_fw_superposition:                   219
% 2.40/1.01  sup_bw_superposition:                   225
% 2.40/1.01  sup_immediate_simplified:               83
% 2.40/1.01  sup_given_eliminated:                   0
% 2.40/1.01  comparisons_done:                       0
% 2.40/1.01  comparisons_avoided:                    0
% 2.40/1.01  
% 2.40/1.01  ------ Simplifications
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  sim_fw_subset_subsumed:                 50
% 2.40/1.01  sim_bw_subset_subsumed:                 7
% 2.40/1.01  sim_fw_subsumed:                        38
% 2.40/1.01  sim_bw_subsumed:                        1
% 2.40/1.01  sim_fw_subsumption_res:                 0
% 2.40/1.01  sim_bw_subsumption_res:                 0
% 2.40/1.01  sim_tautology_del:                      49
% 2.40/1.01  sim_eq_tautology_del:                   0
% 2.40/1.01  sim_eq_res_simp:                        0
% 2.40/1.01  sim_fw_demodulated:                     4
% 2.40/1.01  sim_bw_demodulated:                     4
% 2.40/1.01  sim_light_normalised:                   5
% 2.40/1.01  sim_joinable_taut:                      0
% 2.40/1.01  sim_joinable_simp:                      0
% 2.40/1.01  sim_ac_normalised:                      0
% 2.40/1.01  sim_smt_subsumption:                    0
% 2.40/1.01  
%------------------------------------------------------------------------------

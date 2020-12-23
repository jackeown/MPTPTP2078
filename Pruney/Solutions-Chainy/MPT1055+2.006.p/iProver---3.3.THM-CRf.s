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
% DateTime   : Thu Dec  3 12:09:08 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 776 expanded)
%              Number of clauses        :   84 ( 224 expanded)
%              Number of leaves         :   17 ( 235 expanded)
%              Depth                    :   19
%              Number of atoms          :  492 (6069 expanded)
%              Number of equality atoms :  151 ( 380 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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
    inference(nnf_transformation,[],[f29])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f33,f38,f37,f36,f35,f34])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f50,plain,(
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

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f55])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f58,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1639,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2099,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1639])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1645,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k7_relset_1(X1_48,X2_48,X0_48,X3_48) = k9_relat_1(X0_48,X3_48) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2093,plain,
    ( k7_relset_1(X0_48,X1_48,X2_48,X3_48) = k9_relat_1(X2_48,X3_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1645])).

cnf(c_2957,plain,
    ( k7_relset_1(sK0,sK1,sK2,X0_48) = k9_relat_1(sK2,X0_48) ),
    inference(superposition,[status(thm)],[c_2099,c_2093])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1642,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2096,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1642])).

cnf(c_3063,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2957,c_2096])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1644,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k8_relset_1(X1_48,X2_48,X0_48,X3_48) = k10_relat_1(X0_48,X3_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2094,plain,
    ( k8_relset_1(X0_48,X1_48,X2_48,X3_48) = k10_relat_1(X2_48,X3_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1644])).

cnf(c_3050,plain,
    ( k8_relset_1(sK0,sK1,sK2,X0_48) = k10_relat_1(sK2,X0_48) ),
    inference(superposition,[status(thm)],[c_2099,c_2094])).

cnf(c_3415,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3063,c_3050])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1651,plain,
    ( ~ r1_tarski(X0_48,X1_48)
    | ~ r1_tarski(X2_48,X0_48)
    | r1_tarski(X2_48,X1_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2087,plain,
    ( r1_tarski(X0_48,X1_48) != iProver_top
    | r1_tarski(X2_48,X0_48) != iProver_top
    | r1_tarski(X2_48,X1_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1651])).

cnf(c_3419,plain,
    ( r1_tarski(X0_48,k9_relat_1(sK2,sK3)) != iProver_top
    | r1_tarski(X0_48,sK4) = iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3415,c_2087])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1649,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | r1_tarski(X0_48,X1_48) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2213,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | r1_tarski(sK3,sK0) ),
    inference(instantiation,[status(thm)],[c_1649])).

cnf(c_2214,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2213])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_481,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_482,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_484,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_482,c_21])).

cnf(c_1634,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_484])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1646,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k1_relset_1(X1_48,X2_48,X0_48) = k1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2092,plain,
    ( k1_relset_1(X0_48,X1_48,X2_48) = k1_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1646])).

cnf(c_2539,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2099,c_2092])).

cnf(c_2728,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1634,c_2539])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_461,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK2 != X0
    | sK1 != k1_xboole_0
    | sK0 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_462,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_347,plain,
    ( sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_24])).

cnf(c_464,plain,
    ( sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_347])).

cnf(c_1638,plain,
    ( sK1 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_464])).

cnf(c_3398,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2728,c_1638])).

cnf(c_6,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_369,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_370,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,X1))
    | ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_1635,plain,
    ( r1_tarski(X0_48,k10_relat_1(sK2,X1_48))
    | ~ r1_tarski(X0_48,k1_relat_1(sK2))
    | ~ r1_tarski(k9_relat_1(sK2,X0_48),X1_48)
    | ~ v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_370])).

cnf(c_2101,plain,
    ( r1_tarski(X0_48,k10_relat_1(sK2,X1_48)) = iProver_top
    | r1_tarski(X0_48,k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_48),X1_48) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1635])).

cnf(c_30,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1701,plain,
    ( r1_tarski(X0_48,k10_relat_1(sK2,X1_48)) = iProver_top
    | r1_tarski(X0_48,k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_48),X1_48) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1635])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1647,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2207,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1647])).

cnf(c_2208,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2207])).

cnf(c_2817,plain,
    ( r1_tarski(k9_relat_1(sK2,X0_48),X1_48) != iProver_top
    | r1_tarski(X0_48,k1_relat_1(sK2)) != iProver_top
    | r1_tarski(X0_48,k10_relat_1(sK2,X1_48)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2101,c_30,c_1701,c_2208])).

cnf(c_2818,plain,
    ( r1_tarski(X0_48,k10_relat_1(sK2,X1_48)) = iProver_top
    | r1_tarski(X0_48,k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_48),X1_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_2817])).

cnf(c_3401,plain,
    ( r1_tarski(X0_48,k10_relat_1(sK2,X1_48)) = iProver_top
    | r1_tarski(X0_48,sK0) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_48),X1_48) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3398,c_2818])).

cnf(c_4165,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top
    | r1_tarski(sK3,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3415,c_3401])).

cnf(c_5788,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3419,c_31,c_2214,c_4165])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1648,plain,
    ( ~ r1_tarski(X0_48,X1_48)
    | r1_tarski(k9_relat_1(X2_48,X0_48),k9_relat_1(X2_48,X1_48))
    | ~ v1_relat_1(X2_48) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2090,plain,
    ( r1_tarski(X0_48,X1_48) != iProver_top
    | r1_tarski(k9_relat_1(X2_48,X0_48),k9_relat_1(X2_48,X1_48)) = iProver_top
    | v1_relat_1(X2_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1648])).

cnf(c_5,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_357,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_358,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_1636,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_48)),X0_48)
    | ~ v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_358])).

cnf(c_2100,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_48)),X0_48) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1636])).

cnf(c_1700,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_48)),X0_48) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1636])).

cnf(c_2805,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_48)),X0_48) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2100,c_30,c_1700,c_2208])).

cnf(c_2812,plain,
    ( r1_tarski(X0_48,X1_48) = iProver_top
    | r1_tarski(X0_48,k9_relat_1(sK2,k10_relat_1(sK2,X1_48))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2805,c_2087])).

cnf(c_3826,plain,
    ( r1_tarski(X0_48,k10_relat_1(sK2,X1_48)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_48),X1_48) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2090,c_2812])).

cnf(c_7160,plain,
    ( r1_tarski(k9_relat_1(sK2,X0_48),X1_48) = iProver_top
    | r1_tarski(X0_48,k10_relat_1(sK2,X1_48)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3826,c_30,c_2208])).

cnf(c_7161,plain,
    ( r1_tarski(X0_48,k10_relat_1(sK2,X1_48)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_48),X1_48) = iProver_top ),
    inference(renaming,[status(thm)],[c_7160])).

cnf(c_7172,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5788,c_7161])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1643,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2095,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1643])).

cnf(c_3064,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2957,c_2095])).

cnf(c_3343,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top
    | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3064,c_3050])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7172,c_4165,c_3343,c_2214,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.05/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.06  
% 3.05/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.05/1.06  
% 3.05/1.06  ------  iProver source info
% 3.05/1.06  
% 3.05/1.06  git: date: 2020-06-30 10:37:57 +0100
% 3.05/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.05/1.06  git: non_committed_changes: false
% 3.05/1.06  git: last_make_outside_of_git: false
% 3.05/1.06  
% 3.05/1.06  ------ 
% 3.05/1.06  
% 3.05/1.06  ------ Input Options
% 3.05/1.06  
% 3.05/1.06  --out_options                           all
% 3.05/1.06  --tptp_safe_out                         true
% 3.05/1.06  --problem_path                          ""
% 3.05/1.06  --include_path                          ""
% 3.05/1.06  --clausifier                            res/vclausify_rel
% 3.05/1.06  --clausifier_options                    --mode clausify
% 3.05/1.06  --stdin                                 false
% 3.05/1.06  --stats_out                             all
% 3.05/1.06  
% 3.05/1.06  ------ General Options
% 3.05/1.06  
% 3.05/1.06  --fof                                   false
% 3.05/1.06  --time_out_real                         305.
% 3.05/1.06  --time_out_virtual                      -1.
% 3.05/1.06  --symbol_type_check                     false
% 3.05/1.06  --clausify_out                          false
% 3.05/1.06  --sig_cnt_out                           false
% 3.05/1.06  --trig_cnt_out                          false
% 3.05/1.06  --trig_cnt_out_tolerance                1.
% 3.05/1.06  --trig_cnt_out_sk_spl                   false
% 3.05/1.06  --abstr_cl_out                          false
% 3.05/1.06  
% 3.05/1.06  ------ Global Options
% 3.05/1.06  
% 3.05/1.06  --schedule                              default
% 3.05/1.06  --add_important_lit                     false
% 3.05/1.06  --prop_solver_per_cl                    1000
% 3.05/1.06  --min_unsat_core                        false
% 3.05/1.06  --soft_assumptions                      false
% 3.05/1.06  --soft_lemma_size                       3
% 3.05/1.06  --prop_impl_unit_size                   0
% 3.05/1.06  --prop_impl_unit                        []
% 3.05/1.06  --share_sel_clauses                     true
% 3.05/1.06  --reset_solvers                         false
% 3.05/1.06  --bc_imp_inh                            [conj_cone]
% 3.05/1.06  --conj_cone_tolerance                   3.
% 3.05/1.06  --extra_neg_conj                        none
% 3.05/1.06  --large_theory_mode                     true
% 3.05/1.06  --prolific_symb_bound                   200
% 3.05/1.06  --lt_threshold                          2000
% 3.05/1.06  --clause_weak_htbl                      true
% 3.05/1.06  --gc_record_bc_elim                     false
% 3.05/1.06  
% 3.05/1.06  ------ Preprocessing Options
% 3.05/1.06  
% 3.05/1.06  --preprocessing_flag                    true
% 3.05/1.06  --time_out_prep_mult                    0.1
% 3.05/1.06  --splitting_mode                        input
% 3.05/1.06  --splitting_grd                         true
% 3.05/1.06  --splitting_cvd                         false
% 3.05/1.06  --splitting_cvd_svl                     false
% 3.05/1.06  --splitting_nvd                         32
% 3.05/1.06  --sub_typing                            true
% 3.05/1.06  --prep_gs_sim                           true
% 3.05/1.06  --prep_unflatten                        true
% 3.05/1.06  --prep_res_sim                          true
% 3.05/1.06  --prep_upred                            true
% 3.05/1.06  --prep_sem_filter                       exhaustive
% 3.05/1.06  --prep_sem_filter_out                   false
% 3.05/1.06  --pred_elim                             true
% 3.05/1.06  --res_sim_input                         true
% 3.05/1.06  --eq_ax_congr_red                       true
% 3.05/1.06  --pure_diseq_elim                       true
% 3.05/1.06  --brand_transform                       false
% 3.05/1.06  --non_eq_to_eq                          false
% 3.05/1.06  --prep_def_merge                        true
% 3.05/1.06  --prep_def_merge_prop_impl              false
% 3.05/1.06  --prep_def_merge_mbd                    true
% 3.05/1.06  --prep_def_merge_tr_red                 false
% 3.05/1.06  --prep_def_merge_tr_cl                  false
% 3.05/1.06  --smt_preprocessing                     true
% 3.05/1.06  --smt_ac_axioms                         fast
% 3.05/1.06  --preprocessed_out                      false
% 3.05/1.06  --preprocessed_stats                    false
% 3.05/1.06  
% 3.05/1.06  ------ Abstraction refinement Options
% 3.05/1.06  
% 3.05/1.06  --abstr_ref                             []
% 3.05/1.06  --abstr_ref_prep                        false
% 3.05/1.06  --abstr_ref_until_sat                   false
% 3.05/1.06  --abstr_ref_sig_restrict                funpre
% 3.05/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/1.06  --abstr_ref_under                       []
% 3.05/1.06  
% 3.05/1.06  ------ SAT Options
% 3.05/1.06  
% 3.05/1.06  --sat_mode                              false
% 3.05/1.06  --sat_fm_restart_options                ""
% 3.05/1.06  --sat_gr_def                            false
% 3.05/1.06  --sat_epr_types                         true
% 3.05/1.06  --sat_non_cyclic_types                  false
% 3.05/1.06  --sat_finite_models                     false
% 3.05/1.06  --sat_fm_lemmas                         false
% 3.05/1.06  --sat_fm_prep                           false
% 3.05/1.06  --sat_fm_uc_incr                        true
% 3.05/1.06  --sat_out_model                         small
% 3.05/1.06  --sat_out_clauses                       false
% 3.05/1.06  
% 3.05/1.06  ------ QBF Options
% 3.05/1.06  
% 3.05/1.06  --qbf_mode                              false
% 3.05/1.06  --qbf_elim_univ                         false
% 3.05/1.06  --qbf_dom_inst                          none
% 3.05/1.06  --qbf_dom_pre_inst                      false
% 3.05/1.06  --qbf_sk_in                             false
% 3.05/1.06  --qbf_pred_elim                         true
% 3.05/1.06  --qbf_split                             512
% 3.05/1.06  
% 3.05/1.06  ------ BMC1 Options
% 3.05/1.06  
% 3.05/1.06  --bmc1_incremental                      false
% 3.05/1.06  --bmc1_axioms                           reachable_all
% 3.05/1.06  --bmc1_min_bound                        0
% 3.05/1.06  --bmc1_max_bound                        -1
% 3.05/1.06  --bmc1_max_bound_default                -1
% 3.05/1.06  --bmc1_symbol_reachability              true
% 3.05/1.06  --bmc1_property_lemmas                  false
% 3.05/1.06  --bmc1_k_induction                      false
% 3.05/1.06  --bmc1_non_equiv_states                 false
% 3.05/1.06  --bmc1_deadlock                         false
% 3.05/1.06  --bmc1_ucm                              false
% 3.05/1.06  --bmc1_add_unsat_core                   none
% 3.05/1.06  --bmc1_unsat_core_children              false
% 3.05/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/1.06  --bmc1_out_stat                         full
% 3.05/1.06  --bmc1_ground_init                      false
% 3.05/1.06  --bmc1_pre_inst_next_state              false
% 3.05/1.06  --bmc1_pre_inst_state                   false
% 3.05/1.06  --bmc1_pre_inst_reach_state             false
% 3.05/1.06  --bmc1_out_unsat_core                   false
% 3.05/1.06  --bmc1_aig_witness_out                  false
% 3.05/1.06  --bmc1_verbose                          false
% 3.05/1.06  --bmc1_dump_clauses_tptp                false
% 3.05/1.06  --bmc1_dump_unsat_core_tptp             false
% 3.05/1.06  --bmc1_dump_file                        -
% 3.05/1.06  --bmc1_ucm_expand_uc_limit              128
% 3.05/1.06  --bmc1_ucm_n_expand_iterations          6
% 3.05/1.06  --bmc1_ucm_extend_mode                  1
% 3.05/1.06  --bmc1_ucm_init_mode                    2
% 3.05/1.06  --bmc1_ucm_cone_mode                    none
% 3.05/1.06  --bmc1_ucm_reduced_relation_type        0
% 3.05/1.06  --bmc1_ucm_relax_model                  4
% 3.05/1.06  --bmc1_ucm_full_tr_after_sat            true
% 3.05/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/1.06  --bmc1_ucm_layered_model                none
% 3.05/1.06  --bmc1_ucm_max_lemma_size               10
% 3.05/1.06  
% 3.05/1.06  ------ AIG Options
% 3.05/1.06  
% 3.05/1.06  --aig_mode                              false
% 3.05/1.06  
% 3.05/1.06  ------ Instantiation Options
% 3.05/1.06  
% 3.05/1.06  --instantiation_flag                    true
% 3.05/1.06  --inst_sos_flag                         false
% 3.05/1.06  --inst_sos_phase                        true
% 3.05/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/1.06  --inst_lit_sel_side                     num_symb
% 3.05/1.06  --inst_solver_per_active                1400
% 3.05/1.06  --inst_solver_calls_frac                1.
% 3.05/1.06  --inst_passive_queue_type               priority_queues
% 3.05/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/1.06  --inst_passive_queues_freq              [25;2]
% 3.05/1.06  --inst_dismatching                      true
% 3.05/1.06  --inst_eager_unprocessed_to_passive     true
% 3.05/1.06  --inst_prop_sim_given                   true
% 3.05/1.06  --inst_prop_sim_new                     false
% 3.05/1.06  --inst_subs_new                         false
% 3.05/1.06  --inst_eq_res_simp                      false
% 3.05/1.06  --inst_subs_given                       false
% 3.05/1.06  --inst_orphan_elimination               true
% 3.05/1.06  --inst_learning_loop_flag               true
% 3.05/1.06  --inst_learning_start                   3000
% 3.05/1.06  --inst_learning_factor                  2
% 3.05/1.06  --inst_start_prop_sim_after_learn       3
% 3.05/1.06  --inst_sel_renew                        solver
% 3.05/1.06  --inst_lit_activity_flag                true
% 3.05/1.06  --inst_restr_to_given                   false
% 3.05/1.06  --inst_activity_threshold               500
% 3.05/1.06  --inst_out_proof                        true
% 3.05/1.06  
% 3.05/1.06  ------ Resolution Options
% 3.05/1.06  
% 3.05/1.06  --resolution_flag                       true
% 3.05/1.06  --res_lit_sel                           adaptive
% 3.05/1.06  --res_lit_sel_side                      none
% 3.05/1.06  --res_ordering                          kbo
% 3.05/1.06  --res_to_prop_solver                    active
% 3.05/1.06  --res_prop_simpl_new                    false
% 3.05/1.06  --res_prop_simpl_given                  true
% 3.05/1.06  --res_passive_queue_type                priority_queues
% 3.05/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/1.06  --res_passive_queues_freq               [15;5]
% 3.05/1.06  --res_forward_subs                      full
% 3.05/1.06  --res_backward_subs                     full
% 3.05/1.06  --res_forward_subs_resolution           true
% 3.05/1.06  --res_backward_subs_resolution          true
% 3.05/1.06  --res_orphan_elimination                true
% 3.05/1.06  --res_time_limit                        2.
% 3.05/1.06  --res_out_proof                         true
% 3.05/1.06  
% 3.05/1.06  ------ Superposition Options
% 3.05/1.06  
% 3.05/1.06  --superposition_flag                    true
% 3.05/1.06  --sup_passive_queue_type                priority_queues
% 3.05/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/1.06  --sup_passive_queues_freq               [8;1;4]
% 3.05/1.06  --demod_completeness_check              fast
% 3.05/1.06  --demod_use_ground                      true
% 3.05/1.06  --sup_to_prop_solver                    passive
% 3.05/1.06  --sup_prop_simpl_new                    true
% 3.05/1.06  --sup_prop_simpl_given                  true
% 3.05/1.06  --sup_fun_splitting                     false
% 3.05/1.06  --sup_smt_interval                      50000
% 3.05/1.06  
% 3.05/1.06  ------ Superposition Simplification Setup
% 3.05/1.06  
% 3.05/1.06  --sup_indices_passive                   []
% 3.05/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.06  --sup_full_bw                           [BwDemod]
% 3.05/1.06  --sup_immed_triv                        [TrivRules]
% 3.05/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.06  --sup_immed_bw_main                     []
% 3.05/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.06  
% 3.05/1.06  ------ Combination Options
% 3.05/1.06  
% 3.05/1.06  --comb_res_mult                         3
% 3.05/1.06  --comb_sup_mult                         2
% 3.05/1.06  --comb_inst_mult                        10
% 3.05/1.06  
% 3.05/1.06  ------ Debug Options
% 3.05/1.06  
% 3.05/1.06  --dbg_backtrace                         false
% 3.05/1.06  --dbg_dump_prop_clauses                 false
% 3.05/1.06  --dbg_dump_prop_clauses_file            -
% 3.05/1.06  --dbg_out_stat                          false
% 3.05/1.06  ------ Parsing...
% 3.05/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.05/1.06  
% 3.05/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.05/1.06  
% 3.05/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.05/1.06  
% 3.05/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.05/1.06  ------ Proving...
% 3.05/1.06  ------ Problem Properties 
% 3.05/1.06  
% 3.05/1.06  
% 3.05/1.06  clauses                                 18
% 3.05/1.06  conjectures                             5
% 3.05/1.06  EPR                                     3
% 3.05/1.06  Horn                                    16
% 3.05/1.06  unary                                   5
% 3.05/1.06  binary                                  10
% 3.05/1.06  lits                                    35
% 3.05/1.06  lits eq                                 7
% 3.05/1.06  fd_pure                                 0
% 3.05/1.06  fd_pseudo                               0
% 3.05/1.06  fd_cond                                 0
% 3.05/1.06  fd_pseudo_cond                          0
% 3.05/1.06  AC symbols                              0
% 3.05/1.06  
% 3.05/1.06  ------ Schedule dynamic 5 is on 
% 3.05/1.06  
% 3.05/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.05/1.06  
% 3.05/1.06  
% 3.05/1.06  ------ 
% 3.05/1.06  Current options:
% 3.05/1.06  ------ 
% 3.05/1.06  
% 3.05/1.06  ------ Input Options
% 3.05/1.06  
% 3.05/1.06  --out_options                           all
% 3.05/1.06  --tptp_safe_out                         true
% 3.05/1.06  --problem_path                          ""
% 3.05/1.06  --include_path                          ""
% 3.05/1.06  --clausifier                            res/vclausify_rel
% 3.05/1.06  --clausifier_options                    --mode clausify
% 3.05/1.06  --stdin                                 false
% 3.05/1.06  --stats_out                             all
% 3.05/1.06  
% 3.05/1.06  ------ General Options
% 3.05/1.06  
% 3.05/1.06  --fof                                   false
% 3.05/1.06  --time_out_real                         305.
% 3.05/1.06  --time_out_virtual                      -1.
% 3.05/1.06  --symbol_type_check                     false
% 3.05/1.06  --clausify_out                          false
% 3.05/1.06  --sig_cnt_out                           false
% 3.05/1.06  --trig_cnt_out                          false
% 3.05/1.06  --trig_cnt_out_tolerance                1.
% 3.05/1.06  --trig_cnt_out_sk_spl                   false
% 3.05/1.06  --abstr_cl_out                          false
% 3.05/1.06  
% 3.05/1.06  ------ Global Options
% 3.05/1.06  
% 3.05/1.06  --schedule                              default
% 3.05/1.06  --add_important_lit                     false
% 3.05/1.06  --prop_solver_per_cl                    1000
% 3.05/1.06  --min_unsat_core                        false
% 3.05/1.06  --soft_assumptions                      false
% 3.05/1.06  --soft_lemma_size                       3
% 3.05/1.06  --prop_impl_unit_size                   0
% 3.05/1.06  --prop_impl_unit                        []
% 3.05/1.06  --share_sel_clauses                     true
% 3.05/1.06  --reset_solvers                         false
% 3.05/1.06  --bc_imp_inh                            [conj_cone]
% 3.05/1.06  --conj_cone_tolerance                   3.
% 3.05/1.06  --extra_neg_conj                        none
% 3.05/1.06  --large_theory_mode                     true
% 3.05/1.06  --prolific_symb_bound                   200
% 3.05/1.06  --lt_threshold                          2000
% 3.05/1.06  --clause_weak_htbl                      true
% 3.05/1.06  --gc_record_bc_elim                     false
% 3.05/1.06  
% 3.05/1.06  ------ Preprocessing Options
% 3.05/1.06  
% 3.05/1.06  --preprocessing_flag                    true
% 3.05/1.06  --time_out_prep_mult                    0.1
% 3.05/1.06  --splitting_mode                        input
% 3.05/1.06  --splitting_grd                         true
% 3.05/1.06  --splitting_cvd                         false
% 3.05/1.06  --splitting_cvd_svl                     false
% 3.05/1.06  --splitting_nvd                         32
% 3.05/1.06  --sub_typing                            true
% 3.05/1.06  --prep_gs_sim                           true
% 3.05/1.06  --prep_unflatten                        true
% 3.05/1.06  --prep_res_sim                          true
% 3.05/1.06  --prep_upred                            true
% 3.05/1.06  --prep_sem_filter                       exhaustive
% 3.05/1.06  --prep_sem_filter_out                   false
% 3.05/1.06  --pred_elim                             true
% 3.05/1.06  --res_sim_input                         true
% 3.05/1.06  --eq_ax_congr_red                       true
% 3.05/1.06  --pure_diseq_elim                       true
% 3.05/1.06  --brand_transform                       false
% 3.05/1.06  --non_eq_to_eq                          false
% 3.05/1.06  --prep_def_merge                        true
% 3.05/1.06  --prep_def_merge_prop_impl              false
% 3.05/1.06  --prep_def_merge_mbd                    true
% 3.05/1.06  --prep_def_merge_tr_red                 false
% 3.05/1.06  --prep_def_merge_tr_cl                  false
% 3.05/1.06  --smt_preprocessing                     true
% 3.05/1.06  --smt_ac_axioms                         fast
% 3.05/1.06  --preprocessed_out                      false
% 3.05/1.06  --preprocessed_stats                    false
% 3.05/1.06  
% 3.05/1.06  ------ Abstraction refinement Options
% 3.05/1.06  
% 3.05/1.06  --abstr_ref                             []
% 3.05/1.06  --abstr_ref_prep                        false
% 3.05/1.06  --abstr_ref_until_sat                   false
% 3.05/1.06  --abstr_ref_sig_restrict                funpre
% 3.05/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/1.06  --abstr_ref_under                       []
% 3.05/1.06  
% 3.05/1.06  ------ SAT Options
% 3.05/1.06  
% 3.05/1.06  --sat_mode                              false
% 3.05/1.06  --sat_fm_restart_options                ""
% 3.05/1.06  --sat_gr_def                            false
% 3.05/1.06  --sat_epr_types                         true
% 3.05/1.06  --sat_non_cyclic_types                  false
% 3.05/1.06  --sat_finite_models                     false
% 3.05/1.06  --sat_fm_lemmas                         false
% 3.05/1.06  --sat_fm_prep                           false
% 3.05/1.06  --sat_fm_uc_incr                        true
% 3.05/1.06  --sat_out_model                         small
% 3.05/1.06  --sat_out_clauses                       false
% 3.05/1.06  
% 3.05/1.06  ------ QBF Options
% 3.05/1.06  
% 3.05/1.06  --qbf_mode                              false
% 3.05/1.06  --qbf_elim_univ                         false
% 3.05/1.06  --qbf_dom_inst                          none
% 3.05/1.06  --qbf_dom_pre_inst                      false
% 3.05/1.06  --qbf_sk_in                             false
% 3.05/1.06  --qbf_pred_elim                         true
% 3.05/1.06  --qbf_split                             512
% 3.05/1.06  
% 3.05/1.06  ------ BMC1 Options
% 3.05/1.06  
% 3.05/1.06  --bmc1_incremental                      false
% 3.05/1.06  --bmc1_axioms                           reachable_all
% 3.05/1.06  --bmc1_min_bound                        0
% 3.05/1.06  --bmc1_max_bound                        -1
% 3.05/1.06  --bmc1_max_bound_default                -1
% 3.05/1.06  --bmc1_symbol_reachability              true
% 3.05/1.06  --bmc1_property_lemmas                  false
% 3.05/1.06  --bmc1_k_induction                      false
% 3.05/1.06  --bmc1_non_equiv_states                 false
% 3.05/1.06  --bmc1_deadlock                         false
% 3.05/1.06  --bmc1_ucm                              false
% 3.05/1.06  --bmc1_add_unsat_core                   none
% 3.05/1.06  --bmc1_unsat_core_children              false
% 3.05/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/1.06  --bmc1_out_stat                         full
% 3.05/1.06  --bmc1_ground_init                      false
% 3.05/1.06  --bmc1_pre_inst_next_state              false
% 3.05/1.06  --bmc1_pre_inst_state                   false
% 3.05/1.06  --bmc1_pre_inst_reach_state             false
% 3.05/1.06  --bmc1_out_unsat_core                   false
% 3.05/1.06  --bmc1_aig_witness_out                  false
% 3.05/1.06  --bmc1_verbose                          false
% 3.05/1.06  --bmc1_dump_clauses_tptp                false
% 3.05/1.06  --bmc1_dump_unsat_core_tptp             false
% 3.05/1.06  --bmc1_dump_file                        -
% 3.05/1.06  --bmc1_ucm_expand_uc_limit              128
% 3.05/1.06  --bmc1_ucm_n_expand_iterations          6
% 3.05/1.06  --bmc1_ucm_extend_mode                  1
% 3.05/1.06  --bmc1_ucm_init_mode                    2
% 3.05/1.06  --bmc1_ucm_cone_mode                    none
% 3.05/1.06  --bmc1_ucm_reduced_relation_type        0
% 3.05/1.06  --bmc1_ucm_relax_model                  4
% 3.05/1.06  --bmc1_ucm_full_tr_after_sat            true
% 3.05/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/1.06  --bmc1_ucm_layered_model                none
% 3.05/1.06  --bmc1_ucm_max_lemma_size               10
% 3.05/1.06  
% 3.05/1.06  ------ AIG Options
% 3.05/1.06  
% 3.05/1.06  --aig_mode                              false
% 3.05/1.06  
% 3.05/1.06  ------ Instantiation Options
% 3.05/1.06  
% 3.05/1.06  --instantiation_flag                    true
% 3.05/1.06  --inst_sos_flag                         false
% 3.05/1.06  --inst_sos_phase                        true
% 3.05/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/1.06  --inst_lit_sel_side                     none
% 3.05/1.06  --inst_solver_per_active                1400
% 3.05/1.06  --inst_solver_calls_frac                1.
% 3.05/1.06  --inst_passive_queue_type               priority_queues
% 3.05/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/1.06  --inst_passive_queues_freq              [25;2]
% 3.05/1.06  --inst_dismatching                      true
% 3.05/1.06  --inst_eager_unprocessed_to_passive     true
% 3.05/1.06  --inst_prop_sim_given                   true
% 3.05/1.06  --inst_prop_sim_new                     false
% 3.05/1.06  --inst_subs_new                         false
% 3.05/1.06  --inst_eq_res_simp                      false
% 3.05/1.06  --inst_subs_given                       false
% 3.05/1.06  --inst_orphan_elimination               true
% 3.05/1.06  --inst_learning_loop_flag               true
% 3.05/1.06  --inst_learning_start                   3000
% 3.05/1.06  --inst_learning_factor                  2
% 3.05/1.06  --inst_start_prop_sim_after_learn       3
% 3.05/1.06  --inst_sel_renew                        solver
% 3.05/1.06  --inst_lit_activity_flag                true
% 3.05/1.06  --inst_restr_to_given                   false
% 3.05/1.06  --inst_activity_threshold               500
% 3.05/1.06  --inst_out_proof                        true
% 3.05/1.06  
% 3.05/1.06  ------ Resolution Options
% 3.05/1.06  
% 3.05/1.06  --resolution_flag                       false
% 3.05/1.06  --res_lit_sel                           adaptive
% 3.05/1.06  --res_lit_sel_side                      none
% 3.05/1.06  --res_ordering                          kbo
% 3.05/1.06  --res_to_prop_solver                    active
% 3.05/1.06  --res_prop_simpl_new                    false
% 3.05/1.06  --res_prop_simpl_given                  true
% 3.05/1.06  --res_passive_queue_type                priority_queues
% 3.05/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/1.06  --res_passive_queues_freq               [15;5]
% 3.05/1.06  --res_forward_subs                      full
% 3.05/1.06  --res_backward_subs                     full
% 3.05/1.06  --res_forward_subs_resolution           true
% 3.05/1.06  --res_backward_subs_resolution          true
% 3.05/1.06  --res_orphan_elimination                true
% 3.05/1.06  --res_time_limit                        2.
% 3.05/1.06  --res_out_proof                         true
% 3.05/1.06  
% 3.05/1.06  ------ Superposition Options
% 3.05/1.06  
% 3.05/1.06  --superposition_flag                    true
% 3.05/1.06  --sup_passive_queue_type                priority_queues
% 3.05/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/1.06  --sup_passive_queues_freq               [8;1;4]
% 3.05/1.06  --demod_completeness_check              fast
% 3.05/1.06  --demod_use_ground                      true
% 3.05/1.06  --sup_to_prop_solver                    passive
% 3.05/1.06  --sup_prop_simpl_new                    true
% 3.05/1.06  --sup_prop_simpl_given                  true
% 3.05/1.06  --sup_fun_splitting                     false
% 3.05/1.06  --sup_smt_interval                      50000
% 3.05/1.06  
% 3.05/1.06  ------ Superposition Simplification Setup
% 3.05/1.06  
% 3.05/1.06  --sup_indices_passive                   []
% 3.05/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.06  --sup_full_bw                           [BwDemod]
% 3.05/1.06  --sup_immed_triv                        [TrivRules]
% 3.05/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.06  --sup_immed_bw_main                     []
% 3.05/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.06  
% 3.05/1.06  ------ Combination Options
% 3.05/1.06  
% 3.05/1.06  --comb_res_mult                         3
% 3.05/1.06  --comb_sup_mult                         2
% 3.05/1.06  --comb_inst_mult                        10
% 3.05/1.06  
% 3.05/1.06  ------ Debug Options
% 3.05/1.06  
% 3.05/1.06  --dbg_backtrace                         false
% 3.05/1.06  --dbg_dump_prop_clauses                 false
% 3.05/1.06  --dbg_dump_prop_clauses_file            -
% 3.05/1.06  --dbg_out_stat                          false
% 3.05/1.06  
% 3.05/1.06  
% 3.05/1.06  
% 3.05/1.06  
% 3.05/1.06  ------ Proving...
% 3.05/1.06  
% 3.05/1.06  
% 3.05/1.06  % SZS status Theorem for theBenchmark.p
% 3.05/1.06  
% 3.05/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 3.05/1.06  
% 3.05/1.06  fof(f12,conjecture,(
% 3.05/1.06    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 3.05/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.06  
% 3.05/1.06  fof(f13,negated_conjecture,(
% 3.05/1.06    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 3.05/1.06    inference(negated_conjecture,[],[f12])).
% 3.05/1.06  
% 3.05/1.06  fof(f28,plain,(
% 3.05/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.05/1.06    inference(ennf_transformation,[],[f13])).
% 3.05/1.06  
% 3.05/1.06  fof(f29,plain,(
% 3.05/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.05/1.06    inference(flattening,[],[f28])).
% 3.05/1.06  
% 3.05/1.06  fof(f32,plain,(
% 3.05/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.05/1.06    inference(nnf_transformation,[],[f29])).
% 3.05/1.06  
% 3.05/1.06  fof(f33,plain,(
% 3.05/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.05/1.06    inference(flattening,[],[f32])).
% 3.05/1.06  
% 3.05/1.06  fof(f38,plain,(
% 3.05/1.06    ( ! [X2,X0,X3,X1] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) => ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,sK4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),sK4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,sK4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(X1)))) )),
% 3.05/1.06    introduced(choice_axiom,[])).
% 3.05/1.06  
% 3.05/1.06  fof(f37,plain,(
% 3.05/1.06    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : ((~r1_tarski(sK3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,sK3),X4)) & (r1_tarski(sK3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,sK3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 3.05/1.06    introduced(choice_axiom,[])).
% 3.05/1.06  
% 3.05/1.06  fof(f36,plain,(
% 3.05/1.06    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,sK2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,sK2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,sK2,X4)) | r1_tarski(k7_relset_1(X0,X1,sK2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK2,X0,X1) & v1_funct_1(sK2))) )),
% 3.05/1.06    introduced(choice_axiom,[])).
% 3.05/1.06  
% 3.05/1.06  fof(f35,plain,(
% 3.05/1.06    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,sK1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,sK1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,sK1,X2,X4)) | r1_tarski(k7_relset_1(X0,sK1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) & v1_funct_2(X2,X0,sK1) & v1_funct_1(X2)) & ~v1_xboole_0(sK1))) )),
% 3.05/1.06    introduced(choice_axiom,[])).
% 3.05/1.06  
% 3.05/1.06  fof(f34,plain,(
% 3.05/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 3.05/1.06    introduced(choice_axiom,[])).
% 3.05/1.06  
% 3.05/1.06  fof(f39,plain,(
% 3.05/1.06    (((((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 3.05/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f33,f38,f37,f36,f35,f34])).
% 3.05/1.06  
% 3.05/1.06  fof(f61,plain,(
% 3.05/1.06    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.05/1.06    inference(cnf_transformation,[],[f39])).
% 3.05/1.06  
% 3.05/1.06  fof(f9,axiom,(
% 3.05/1.06    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.05/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.06  
% 3.05/1.06  fof(f24,plain,(
% 3.05/1.06    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/1.06    inference(ennf_transformation,[],[f9])).
% 3.05/1.06  
% 3.05/1.06  fof(f49,plain,(
% 3.05/1.06    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/1.06    inference(cnf_transformation,[],[f24])).
% 3.05/1.06  
% 3.05/1.06  fof(f64,plain,(
% 3.05/1.06    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 3.05/1.06    inference(cnf_transformation,[],[f39])).
% 3.05/1.06  
% 3.05/1.06  fof(f10,axiom,(
% 3.05/1.06    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.05/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.06  
% 3.05/1.06  fof(f25,plain,(
% 3.05/1.06    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/1.06    inference(ennf_transformation,[],[f10])).
% 3.05/1.06  
% 3.05/1.06  fof(f50,plain,(
% 3.05/1.06    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/1.06    inference(cnf_transformation,[],[f25])).
% 3.05/1.06  
% 3.05/1.06  fof(f2,axiom,(
% 3.05/1.06    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.05/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.06  
% 3.05/1.06  fof(f14,plain,(
% 3.05/1.06    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.05/1.06    inference(ennf_transformation,[],[f2])).
% 3.05/1.06  
% 3.05/1.06  fof(f15,plain,(
% 3.05/1.06    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.05/1.06    inference(flattening,[],[f14])).
% 3.05/1.06  
% 3.05/1.06  fof(f41,plain,(
% 3.05/1.06    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.05/1.06    inference(cnf_transformation,[],[f15])).
% 3.05/1.06  
% 3.05/1.06  fof(f62,plain,(
% 3.05/1.06    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 3.05/1.06    inference(cnf_transformation,[],[f39])).
% 3.05/1.06  
% 3.05/1.06  fof(f3,axiom,(
% 3.05/1.06    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.05/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.06  
% 3.05/1.06  fof(f30,plain,(
% 3.05/1.06    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.05/1.06    inference(nnf_transformation,[],[f3])).
% 3.05/1.06  
% 3.05/1.06  fof(f42,plain,(
% 3.05/1.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.05/1.06    inference(cnf_transformation,[],[f30])).
% 3.05/1.06  
% 3.05/1.06  fof(f11,axiom,(
% 3.05/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.05/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.06  
% 3.05/1.06  fof(f26,plain,(
% 3.05/1.06    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/1.06    inference(ennf_transformation,[],[f11])).
% 3.05/1.06  
% 3.05/1.06  fof(f27,plain,(
% 3.05/1.06    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/1.06    inference(flattening,[],[f26])).
% 3.05/1.06  
% 3.05/1.06  fof(f31,plain,(
% 3.05/1.06    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/1.06    inference(nnf_transformation,[],[f27])).
% 3.05/1.06  
% 3.05/1.06  fof(f51,plain,(
% 3.05/1.06    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/1.06    inference(cnf_transformation,[],[f31])).
% 3.05/1.06  
% 3.05/1.06  fof(f60,plain,(
% 3.05/1.06    v1_funct_2(sK2,sK0,sK1)),
% 3.05/1.06    inference(cnf_transformation,[],[f39])).
% 3.05/1.06  
% 3.05/1.06  fof(f8,axiom,(
% 3.05/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.05/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.06  
% 3.05/1.06  fof(f23,plain,(
% 3.05/1.06    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/1.06    inference(ennf_transformation,[],[f8])).
% 3.05/1.06  
% 3.05/1.06  fof(f48,plain,(
% 3.05/1.06    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/1.06    inference(cnf_transformation,[],[f23])).
% 3.05/1.06  
% 3.05/1.06  fof(f55,plain,(
% 3.05/1.06    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/1.06    inference(cnf_transformation,[],[f31])).
% 3.05/1.06  
% 3.05/1.06  fof(f68,plain,(
% 3.05/1.06    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.05/1.06    inference(equality_resolution,[],[f55])).
% 3.05/1.06  
% 3.05/1.06  fof(f1,axiom,(
% 3.05/1.06    v1_xboole_0(k1_xboole_0)),
% 3.05/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.06  
% 3.05/1.06  fof(f40,plain,(
% 3.05/1.06    v1_xboole_0(k1_xboole_0)),
% 3.05/1.06    inference(cnf_transformation,[],[f1])).
% 3.05/1.06  
% 3.05/1.06  fof(f58,plain,(
% 3.05/1.06    ~v1_xboole_0(sK1)),
% 3.05/1.06    inference(cnf_transformation,[],[f39])).
% 3.05/1.06  
% 3.05/1.06  fof(f6,axiom,(
% 3.05/1.06    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 3.05/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.06  
% 3.05/1.06  fof(f20,plain,(
% 3.05/1.06    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.05/1.06    inference(ennf_transformation,[],[f6])).
% 3.05/1.06  
% 3.05/1.06  fof(f21,plain,(
% 3.05/1.06    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.05/1.06    inference(flattening,[],[f20])).
% 3.05/1.06  
% 3.05/1.06  fof(f46,plain,(
% 3.05/1.06    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.05/1.06    inference(cnf_transformation,[],[f21])).
% 3.05/1.06  
% 3.05/1.06  fof(f59,plain,(
% 3.05/1.06    v1_funct_1(sK2)),
% 3.05/1.06    inference(cnf_transformation,[],[f39])).
% 3.05/1.06  
% 3.05/1.06  fof(f7,axiom,(
% 3.05/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.05/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.06  
% 3.05/1.06  fof(f22,plain,(
% 3.05/1.06    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/1.06    inference(ennf_transformation,[],[f7])).
% 3.05/1.06  
% 3.05/1.06  fof(f47,plain,(
% 3.05/1.06    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/1.06    inference(cnf_transformation,[],[f22])).
% 3.05/1.06  
% 3.05/1.06  fof(f4,axiom,(
% 3.05/1.06    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.05/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.06  
% 3.05/1.06  fof(f16,plain,(
% 3.05/1.06    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 3.05/1.06    inference(ennf_transformation,[],[f4])).
% 3.05/1.06  
% 3.05/1.06  fof(f17,plain,(
% 3.05/1.06    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 3.05/1.06    inference(flattening,[],[f16])).
% 3.05/1.06  
% 3.05/1.06  fof(f44,plain,(
% 3.05/1.06    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 3.05/1.06    inference(cnf_transformation,[],[f17])).
% 3.05/1.06  
% 3.05/1.06  fof(f5,axiom,(
% 3.05/1.06    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 3.05/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.06  
% 3.05/1.06  fof(f18,plain,(
% 3.05/1.06    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.05/1.06    inference(ennf_transformation,[],[f5])).
% 3.05/1.06  
% 3.05/1.06  fof(f19,plain,(
% 3.05/1.06    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.05/1.06    inference(flattening,[],[f18])).
% 3.05/1.06  
% 3.05/1.06  fof(f45,plain,(
% 3.05/1.06    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.05/1.06    inference(cnf_transformation,[],[f19])).
% 3.05/1.06  
% 3.05/1.06  fof(f65,plain,(
% 3.05/1.06    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 3.05/1.06    inference(cnf_transformation,[],[f39])).
% 3.05/1.06  
% 3.05/1.06  cnf(c_21,negated_conjecture,
% 3.05/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.05/1.06      inference(cnf_transformation,[],[f61]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_1639,negated_conjecture,
% 3.05/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.05/1.06      inference(subtyping,[status(esa)],[c_21]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2099,plain,
% 3.05/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.05/1.06      inference(predicate_to_equality,[status(thm)],[c_1639]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_9,plain,
% 3.05/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/1.06      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.05/1.06      inference(cnf_transformation,[],[f49]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_1645,plain,
% 3.05/1.06      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 3.05/1.06      | k7_relset_1(X1_48,X2_48,X0_48,X3_48) = k9_relat_1(X0_48,X3_48) ),
% 3.05/1.06      inference(subtyping,[status(esa)],[c_9]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2093,plain,
% 3.05/1.06      ( k7_relset_1(X0_48,X1_48,X2_48,X3_48) = k9_relat_1(X2_48,X3_48)
% 3.05/1.06      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 3.05/1.06      inference(predicate_to_equality,[status(thm)],[c_1645]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2957,plain,
% 3.05/1.06      ( k7_relset_1(sK0,sK1,sK2,X0_48) = k9_relat_1(sK2,X0_48) ),
% 3.05/1.06      inference(superposition,[status(thm)],[c_2099,c_2093]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_18,negated_conjecture,
% 3.05/1.06      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
% 3.05/1.06      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
% 3.05/1.06      inference(cnf_transformation,[],[f64]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_1642,negated_conjecture,
% 3.05/1.06      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
% 3.05/1.06      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
% 3.05/1.06      inference(subtyping,[status(esa)],[c_18]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2096,plain,
% 3.05/1.06      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) = iProver_top
% 3.05/1.06      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) = iProver_top ),
% 3.05/1.06      inference(predicate_to_equality,[status(thm)],[c_1642]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_3063,plain,
% 3.05/1.06      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
% 3.05/1.06      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) = iProver_top ),
% 3.05/1.06      inference(demodulation,[status(thm)],[c_2957,c_2096]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_10,plain,
% 3.05/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/1.06      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.05/1.06      inference(cnf_transformation,[],[f50]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_1644,plain,
% 3.05/1.06      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 3.05/1.06      | k8_relset_1(X1_48,X2_48,X0_48,X3_48) = k10_relat_1(X0_48,X3_48) ),
% 3.05/1.06      inference(subtyping,[status(esa)],[c_10]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2094,plain,
% 3.05/1.06      ( k8_relset_1(X0_48,X1_48,X2_48,X3_48) = k10_relat_1(X2_48,X3_48)
% 3.05/1.06      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 3.05/1.06      inference(predicate_to_equality,[status(thm)],[c_1644]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_3050,plain,
% 3.05/1.06      ( k8_relset_1(sK0,sK1,sK2,X0_48) = k10_relat_1(sK2,X0_48) ),
% 3.05/1.06      inference(superposition,[status(thm)],[c_2099,c_2094]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_3415,plain,
% 3.05/1.06      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top
% 3.05/1.06      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
% 3.05/1.06      inference(demodulation,[status(thm)],[c_3063,c_3050]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_1,plain,
% 3.05/1.06      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.05/1.06      inference(cnf_transformation,[],[f41]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_1651,plain,
% 3.05/1.06      ( ~ r1_tarski(X0_48,X1_48)
% 3.05/1.06      | ~ r1_tarski(X2_48,X0_48)
% 3.05/1.06      | r1_tarski(X2_48,X1_48) ),
% 3.05/1.06      inference(subtyping,[status(esa)],[c_1]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2087,plain,
% 3.05/1.06      ( r1_tarski(X0_48,X1_48) != iProver_top
% 3.05/1.06      | r1_tarski(X2_48,X0_48) != iProver_top
% 3.05/1.06      | r1_tarski(X2_48,X1_48) = iProver_top ),
% 3.05/1.06      inference(predicate_to_equality,[status(thm)],[c_1651]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_3419,plain,
% 3.05/1.06      ( r1_tarski(X0_48,k9_relat_1(sK2,sK3)) != iProver_top
% 3.05/1.06      | r1_tarski(X0_48,sK4) = iProver_top
% 3.05/1.06      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
% 3.05/1.06      inference(superposition,[status(thm)],[c_3415,c_2087]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_20,negated_conjecture,
% 3.05/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 3.05/1.06      inference(cnf_transformation,[],[f62]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_31,plain,
% 3.05/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 3.05/1.06      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_3,plain,
% 3.05/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.05/1.06      inference(cnf_transformation,[],[f42]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_1649,plain,
% 3.05/1.06      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
% 3.05/1.06      | r1_tarski(X0_48,X1_48) ),
% 3.05/1.06      inference(subtyping,[status(esa)],[c_3]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2213,plain,
% 3.05/1.06      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) | r1_tarski(sK3,sK0) ),
% 3.05/1.06      inference(instantiation,[status(thm)],[c_1649]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2214,plain,
% 3.05/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 3.05/1.06      | r1_tarski(sK3,sK0) = iProver_top ),
% 3.05/1.06      inference(predicate_to_equality,[status(thm)],[c_2213]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_16,plain,
% 3.05/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 3.05/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/1.06      | k1_relset_1(X1,X2,X0) = X1
% 3.05/1.06      | k1_xboole_0 = X2 ),
% 3.05/1.06      inference(cnf_transformation,[],[f51]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_22,negated_conjecture,
% 3.05/1.06      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.05/1.06      inference(cnf_transformation,[],[f60]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_481,plain,
% 3.05/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/1.06      | k1_relset_1(X1,X2,X0) = X1
% 3.05/1.06      | sK2 != X0
% 3.05/1.06      | sK1 != X2
% 3.05/1.06      | sK0 != X1
% 3.05/1.06      | k1_xboole_0 = X2 ),
% 3.05/1.06      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_482,plain,
% 3.05/1.06      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.05/1.06      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.05/1.06      | k1_xboole_0 = sK1 ),
% 3.05/1.06      inference(unflattening,[status(thm)],[c_481]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_484,plain,
% 3.05/1.06      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.05/1.06      inference(global_propositional_subsumption,
% 3.05/1.06                [status(thm)],
% 3.05/1.06                [c_482,c_21]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_1634,plain,
% 3.05/1.06      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.05/1.06      inference(subtyping,[status(esa)],[c_484]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_8,plain,
% 3.05/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/1.06      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.05/1.06      inference(cnf_transformation,[],[f48]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_1646,plain,
% 3.05/1.06      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 3.05/1.06      | k1_relset_1(X1_48,X2_48,X0_48) = k1_relat_1(X0_48) ),
% 3.05/1.06      inference(subtyping,[status(esa)],[c_8]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2092,plain,
% 3.05/1.06      ( k1_relset_1(X0_48,X1_48,X2_48) = k1_relat_1(X2_48)
% 3.05/1.06      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 3.05/1.06      inference(predicate_to_equality,[status(thm)],[c_1646]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2539,plain,
% 3.05/1.06      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.05/1.06      inference(superposition,[status(thm)],[c_2099,c_2092]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2728,plain,
% 3.05/1.06      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 3.05/1.06      inference(superposition,[status(thm)],[c_1634,c_2539]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_12,plain,
% 3.05/1.06      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.05/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.05/1.06      | k1_xboole_0 = X1
% 3.05/1.06      | k1_xboole_0 = X0 ),
% 3.05/1.06      inference(cnf_transformation,[],[f68]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_461,plain,
% 3.05/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.05/1.06      | sK2 != X0
% 3.05/1.06      | sK1 != k1_xboole_0
% 3.05/1.06      | sK0 != X1
% 3.05/1.06      | k1_xboole_0 = X0
% 3.05/1.06      | k1_xboole_0 = X1 ),
% 3.05/1.06      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_462,plain,
% 3.05/1.06      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 3.05/1.06      | sK1 != k1_xboole_0
% 3.05/1.06      | k1_xboole_0 = sK2
% 3.05/1.06      | k1_xboole_0 = sK0 ),
% 3.05/1.06      inference(unflattening,[status(thm)],[c_461]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_0,plain,
% 3.05/1.06      ( v1_xboole_0(k1_xboole_0) ),
% 3.05/1.06      inference(cnf_transformation,[],[f40]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_24,negated_conjecture,
% 3.05/1.06      ( ~ v1_xboole_0(sK1) ),
% 3.05/1.06      inference(cnf_transformation,[],[f58]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_347,plain,
% 3.05/1.06      ( sK1 != k1_xboole_0 ),
% 3.05/1.06      inference(resolution_lifted,[status(thm)],[c_0,c_24]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_464,plain,
% 3.05/1.06      ( sK1 != k1_xboole_0 ),
% 3.05/1.06      inference(global_propositional_subsumption,
% 3.05/1.06                [status(thm)],
% 3.05/1.06                [c_462,c_347]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_1638,plain,
% 3.05/1.06      ( sK1 != k1_xboole_0 ),
% 3.05/1.06      inference(subtyping,[status(esa)],[c_464]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_3398,plain,
% 3.05/1.06      ( k1_relat_1(sK2) = sK0 ),
% 3.05/1.06      inference(global_propositional_subsumption,
% 3.05/1.06                [status(thm)],
% 3.05/1.06                [c_2728,c_1638]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_6,plain,
% 3.05/1.06      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 3.05/1.06      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.05/1.06      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 3.05/1.06      | ~ v1_funct_1(X1)
% 3.05/1.06      | ~ v1_relat_1(X1) ),
% 3.05/1.06      inference(cnf_transformation,[],[f46]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_23,negated_conjecture,
% 3.05/1.06      ( v1_funct_1(sK2) ),
% 3.05/1.06      inference(cnf_transformation,[],[f59]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_369,plain,
% 3.05/1.06      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 3.05/1.06      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.05/1.06      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 3.05/1.06      | ~ v1_relat_1(X1)
% 3.05/1.06      | sK2 != X1 ),
% 3.05/1.06      inference(resolution_lifted,[status(thm)],[c_6,c_23]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_370,plain,
% 3.05/1.06      ( r1_tarski(X0,k10_relat_1(sK2,X1))
% 3.05/1.06      | ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.05/1.06      | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
% 3.05/1.06      | ~ v1_relat_1(sK2) ),
% 3.05/1.06      inference(unflattening,[status(thm)],[c_369]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_1635,plain,
% 3.05/1.06      ( r1_tarski(X0_48,k10_relat_1(sK2,X1_48))
% 3.05/1.06      | ~ r1_tarski(X0_48,k1_relat_1(sK2))
% 3.05/1.06      | ~ r1_tarski(k9_relat_1(sK2,X0_48),X1_48)
% 3.05/1.06      | ~ v1_relat_1(sK2) ),
% 3.05/1.06      inference(subtyping,[status(esa)],[c_370]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2101,plain,
% 3.05/1.06      ( r1_tarski(X0_48,k10_relat_1(sK2,X1_48)) = iProver_top
% 3.05/1.06      | r1_tarski(X0_48,k1_relat_1(sK2)) != iProver_top
% 3.05/1.06      | r1_tarski(k9_relat_1(sK2,X0_48),X1_48) != iProver_top
% 3.05/1.06      | v1_relat_1(sK2) != iProver_top ),
% 3.05/1.06      inference(predicate_to_equality,[status(thm)],[c_1635]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_30,plain,
% 3.05/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.05/1.06      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_1701,plain,
% 3.05/1.06      ( r1_tarski(X0_48,k10_relat_1(sK2,X1_48)) = iProver_top
% 3.05/1.06      | r1_tarski(X0_48,k1_relat_1(sK2)) != iProver_top
% 3.05/1.06      | r1_tarski(k9_relat_1(sK2,X0_48),X1_48) != iProver_top
% 3.05/1.06      | v1_relat_1(sK2) != iProver_top ),
% 3.05/1.06      inference(predicate_to_equality,[status(thm)],[c_1635]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_7,plain,
% 3.05/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/1.06      | v1_relat_1(X0) ),
% 3.05/1.06      inference(cnf_transformation,[],[f47]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_1647,plain,
% 3.05/1.06      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 3.05/1.06      | v1_relat_1(X0_48) ),
% 3.05/1.06      inference(subtyping,[status(esa)],[c_7]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2207,plain,
% 3.05/1.06      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.05/1.06      | v1_relat_1(sK2) ),
% 3.05/1.06      inference(instantiation,[status(thm)],[c_1647]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2208,plain,
% 3.05/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.05/1.06      | v1_relat_1(sK2) = iProver_top ),
% 3.05/1.06      inference(predicate_to_equality,[status(thm)],[c_2207]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2817,plain,
% 3.05/1.06      ( r1_tarski(k9_relat_1(sK2,X0_48),X1_48) != iProver_top
% 3.05/1.06      | r1_tarski(X0_48,k1_relat_1(sK2)) != iProver_top
% 3.05/1.06      | r1_tarski(X0_48,k10_relat_1(sK2,X1_48)) = iProver_top ),
% 3.05/1.06      inference(global_propositional_subsumption,
% 3.05/1.06                [status(thm)],
% 3.05/1.06                [c_2101,c_30,c_1701,c_2208]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2818,plain,
% 3.05/1.06      ( r1_tarski(X0_48,k10_relat_1(sK2,X1_48)) = iProver_top
% 3.05/1.06      | r1_tarski(X0_48,k1_relat_1(sK2)) != iProver_top
% 3.05/1.06      | r1_tarski(k9_relat_1(sK2,X0_48),X1_48) != iProver_top ),
% 3.05/1.06      inference(renaming,[status(thm)],[c_2817]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_3401,plain,
% 3.05/1.06      ( r1_tarski(X0_48,k10_relat_1(sK2,X1_48)) = iProver_top
% 3.05/1.06      | r1_tarski(X0_48,sK0) != iProver_top
% 3.05/1.06      | r1_tarski(k9_relat_1(sK2,X0_48),X1_48) != iProver_top ),
% 3.05/1.06      inference(demodulation,[status(thm)],[c_3398,c_2818]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_4165,plain,
% 3.05/1.06      ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top
% 3.05/1.06      | r1_tarski(sK3,sK0) != iProver_top ),
% 3.05/1.06      inference(superposition,[status(thm)],[c_3415,c_3401]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_5788,plain,
% 3.05/1.06      ( r1_tarski(sK3,k10_relat_1(sK2,sK4)) = iProver_top ),
% 3.05/1.06      inference(global_propositional_subsumption,
% 3.05/1.06                [status(thm)],
% 3.05/1.06                [c_3419,c_31,c_2214,c_4165]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_4,plain,
% 3.05/1.06      ( ~ r1_tarski(X0,X1)
% 3.05/1.06      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 3.05/1.06      | ~ v1_relat_1(X2) ),
% 3.05/1.06      inference(cnf_transformation,[],[f44]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_1648,plain,
% 3.05/1.06      ( ~ r1_tarski(X0_48,X1_48)
% 3.05/1.06      | r1_tarski(k9_relat_1(X2_48,X0_48),k9_relat_1(X2_48,X1_48))
% 3.05/1.06      | ~ v1_relat_1(X2_48) ),
% 3.05/1.06      inference(subtyping,[status(esa)],[c_4]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2090,plain,
% 3.05/1.06      ( r1_tarski(X0_48,X1_48) != iProver_top
% 3.05/1.06      | r1_tarski(k9_relat_1(X2_48,X0_48),k9_relat_1(X2_48,X1_48)) = iProver_top
% 3.05/1.06      | v1_relat_1(X2_48) != iProver_top ),
% 3.05/1.06      inference(predicate_to_equality,[status(thm)],[c_1648]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_5,plain,
% 3.05/1.06      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.05/1.06      | ~ v1_funct_1(X0)
% 3.05/1.06      | ~ v1_relat_1(X0) ),
% 3.05/1.06      inference(cnf_transformation,[],[f45]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_357,plain,
% 3.05/1.06      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.05/1.06      | ~ v1_relat_1(X0)
% 3.05/1.06      | sK2 != X0 ),
% 3.05/1.06      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_358,plain,
% 3.05/1.06      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
% 3.05/1.06      | ~ v1_relat_1(sK2) ),
% 3.05/1.06      inference(unflattening,[status(thm)],[c_357]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_1636,plain,
% 3.05/1.06      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_48)),X0_48)
% 3.05/1.06      | ~ v1_relat_1(sK2) ),
% 3.05/1.06      inference(subtyping,[status(esa)],[c_358]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2100,plain,
% 3.05/1.06      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_48)),X0_48) = iProver_top
% 3.05/1.06      | v1_relat_1(sK2) != iProver_top ),
% 3.05/1.06      inference(predicate_to_equality,[status(thm)],[c_1636]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_1700,plain,
% 3.05/1.06      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_48)),X0_48) = iProver_top
% 3.05/1.06      | v1_relat_1(sK2) != iProver_top ),
% 3.05/1.06      inference(predicate_to_equality,[status(thm)],[c_1636]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2805,plain,
% 3.05/1.06      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_48)),X0_48) = iProver_top ),
% 3.05/1.06      inference(global_propositional_subsumption,
% 3.05/1.06                [status(thm)],
% 3.05/1.06                [c_2100,c_30,c_1700,c_2208]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2812,plain,
% 3.05/1.06      ( r1_tarski(X0_48,X1_48) = iProver_top
% 3.05/1.06      | r1_tarski(X0_48,k9_relat_1(sK2,k10_relat_1(sK2,X1_48))) != iProver_top ),
% 3.05/1.06      inference(superposition,[status(thm)],[c_2805,c_2087]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_3826,plain,
% 3.05/1.06      ( r1_tarski(X0_48,k10_relat_1(sK2,X1_48)) != iProver_top
% 3.05/1.06      | r1_tarski(k9_relat_1(sK2,X0_48),X1_48) = iProver_top
% 3.05/1.06      | v1_relat_1(sK2) != iProver_top ),
% 3.05/1.06      inference(superposition,[status(thm)],[c_2090,c_2812]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_7160,plain,
% 3.05/1.06      ( r1_tarski(k9_relat_1(sK2,X0_48),X1_48) = iProver_top
% 3.05/1.06      | r1_tarski(X0_48,k10_relat_1(sK2,X1_48)) != iProver_top ),
% 3.05/1.06      inference(global_propositional_subsumption,
% 3.05/1.06                [status(thm)],
% 3.05/1.06                [c_3826,c_30,c_2208]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_7161,plain,
% 3.05/1.06      ( r1_tarski(X0_48,k10_relat_1(sK2,X1_48)) != iProver_top
% 3.05/1.06      | r1_tarski(k9_relat_1(sK2,X0_48),X1_48) = iProver_top ),
% 3.05/1.06      inference(renaming,[status(thm)],[c_7160]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_7172,plain,
% 3.05/1.06      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) = iProver_top ),
% 3.05/1.06      inference(superposition,[status(thm)],[c_5788,c_7161]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_17,negated_conjecture,
% 3.05/1.06      ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
% 3.05/1.06      | ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
% 3.05/1.06      inference(cnf_transformation,[],[f65]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_1643,negated_conjecture,
% 3.05/1.06      ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
% 3.05/1.06      | ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
% 3.05/1.06      inference(subtyping,[status(esa)],[c_17]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_2095,plain,
% 3.05/1.06      ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) != iProver_top
% 3.05/1.06      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) != iProver_top ),
% 3.05/1.06      inference(predicate_to_equality,[status(thm)],[c_1643]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_3064,plain,
% 3.05/1.06      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top
% 3.05/1.06      | r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) != iProver_top ),
% 3.05/1.06      inference(demodulation,[status(thm)],[c_2957,c_2095]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(c_3343,plain,
% 3.05/1.06      ( r1_tarski(k9_relat_1(sK2,sK3),sK4) != iProver_top
% 3.05/1.06      | r1_tarski(sK3,k10_relat_1(sK2,sK4)) != iProver_top ),
% 3.05/1.06      inference(demodulation,[status(thm)],[c_3064,c_3050]) ).
% 3.05/1.06  
% 3.05/1.06  cnf(contradiction,plain,
% 3.05/1.06      ( $false ),
% 3.05/1.06      inference(minisat,[status(thm)],[c_7172,c_4165,c_3343,c_2214,c_31]) ).
% 3.05/1.06  
% 3.05/1.06  
% 3.05/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 3.05/1.06  
% 3.05/1.06  ------                               Statistics
% 3.05/1.06  
% 3.05/1.06  ------ General
% 3.05/1.06  
% 3.05/1.06  abstr_ref_over_cycles:                  0
% 3.05/1.06  abstr_ref_under_cycles:                 0
% 3.05/1.06  gc_basic_clause_elim:                   0
% 3.05/1.06  forced_gc_time:                         0
% 3.05/1.06  parsing_time:                           0.012
% 3.05/1.06  unif_index_cands_time:                  0.
% 3.05/1.06  unif_index_add_time:                    0.
% 3.05/1.06  orderings_time:                         0.
% 3.05/1.06  out_proof_time:                         0.012
% 3.05/1.06  total_time:                             0.239
% 3.05/1.06  num_of_symbols:                         53
% 3.05/1.06  num_of_terms:                           6880
% 3.05/1.06  
% 3.05/1.06  ------ Preprocessing
% 3.05/1.06  
% 3.05/1.06  num_of_splits:                          0
% 3.05/1.06  num_of_split_atoms:                     0
% 3.05/1.06  num_of_reused_defs:                     0
% 3.05/1.06  num_eq_ax_congr_red:                    10
% 3.05/1.06  num_of_sem_filtered_clauses:            1
% 3.05/1.06  num_of_subtypes:                        2
% 3.05/1.06  monotx_restored_types:                  0
% 3.05/1.06  sat_num_of_epr_types:                   0
% 3.05/1.06  sat_num_of_non_cyclic_types:            0
% 3.05/1.06  sat_guarded_non_collapsed_types:        0
% 3.05/1.06  num_pure_diseq_elim:                    0
% 3.05/1.06  simp_replaced_by:                       0
% 3.05/1.06  res_preprocessed:                       130
% 3.05/1.06  prep_upred:                             0
% 3.05/1.06  prep_unflattend:                        95
% 3.05/1.06  smt_new_axioms:                         0
% 3.05/1.06  pred_elim_cands:                        3
% 3.05/1.06  pred_elim:                              3
% 3.05/1.06  pred_elim_cl:                           8
% 3.05/1.06  pred_elim_cycles:                       10
% 3.05/1.06  merged_defs:                            20
% 3.05/1.06  merged_defs_ncl:                        0
% 3.05/1.06  bin_hyper_res:                          20
% 3.05/1.06  prep_cycles:                            5
% 3.05/1.06  pred_elim_time:                         0.021
% 3.05/1.06  splitting_time:                         0.
% 3.05/1.06  sem_filter_time:                        0.
% 3.05/1.06  monotx_time:                            0.
% 3.05/1.06  subtype_inf_time:                       0.
% 3.05/1.06  
% 3.05/1.06  ------ Problem properties
% 3.05/1.06  
% 3.05/1.06  clauses:                                18
% 3.05/1.06  conjectures:                            5
% 3.05/1.06  epr:                                    3
% 3.05/1.06  horn:                                   16
% 3.05/1.06  ground:                                 8
% 3.05/1.06  unary:                                  5
% 3.05/1.06  binary:                                 10
% 3.05/1.06  lits:                                   35
% 3.05/1.06  lits_eq:                                7
% 3.05/1.06  fd_pure:                                0
% 3.05/1.06  fd_pseudo:                              0
% 3.05/1.06  fd_cond:                                0
% 3.05/1.06  fd_pseudo_cond:                         0
% 3.05/1.06  ac_symbols:                             0
% 3.05/1.06  
% 3.05/1.06  ------ Propositional Solver
% 3.05/1.06  
% 3.05/1.06  prop_solver_calls:                      32
% 3.05/1.06  prop_fast_solver_calls:                 913
% 3.05/1.06  smt_solver_calls:                       0
% 3.05/1.06  smt_fast_solver_calls:                  0
% 3.05/1.06  prop_num_of_clauses:                    2617
% 3.05/1.06  prop_preprocess_simplified:             6873
% 3.05/1.06  prop_fo_subsumed:                       14
% 3.05/1.06  prop_solver_time:                       0.
% 3.05/1.06  smt_solver_time:                        0.
% 3.05/1.06  smt_fast_solver_time:                   0.
% 3.05/1.06  prop_fast_solver_time:                  0.
% 3.05/1.06  prop_unsat_core_time:                   0.
% 3.05/1.06  
% 3.05/1.06  ------ QBF
% 3.05/1.06  
% 3.05/1.06  qbf_q_res:                              0
% 3.05/1.06  qbf_num_tautologies:                    0
% 3.05/1.06  qbf_prep_cycles:                        0
% 3.05/1.06  
% 3.05/1.06  ------ BMC1
% 3.05/1.06  
% 3.05/1.06  bmc1_current_bound:                     -1
% 3.05/1.06  bmc1_last_solved_bound:                 -1
% 3.05/1.06  bmc1_unsat_core_size:                   -1
% 3.05/1.06  bmc1_unsat_core_parents_size:           -1
% 3.05/1.06  bmc1_merge_next_fun:                    0
% 3.05/1.06  bmc1_unsat_core_clauses_time:           0.
% 3.05/1.06  
% 3.05/1.06  ------ Instantiation
% 3.05/1.06  
% 3.05/1.06  inst_num_of_clauses:                    685
% 3.05/1.06  inst_num_in_passive:                    244
% 3.05/1.06  inst_num_in_active:                     316
% 3.05/1.06  inst_num_in_unprocessed:                125
% 3.05/1.06  inst_num_of_loops:                      370
% 3.05/1.06  inst_num_of_learning_restarts:          0
% 3.05/1.06  inst_num_moves_active_passive:          52
% 3.05/1.06  inst_lit_activity:                      0
% 3.05/1.06  inst_lit_activity_moves:                0
% 3.05/1.06  inst_num_tautologies:                   0
% 3.05/1.06  inst_num_prop_implied:                  0
% 3.05/1.06  inst_num_existing_simplified:           0
% 3.05/1.06  inst_num_eq_res_simplified:             0
% 3.05/1.06  inst_num_child_elim:                    0
% 3.05/1.06  inst_num_of_dismatching_blockings:      277
% 3.05/1.06  inst_num_of_non_proper_insts:           402
% 3.05/1.06  inst_num_of_duplicates:                 0
% 3.05/1.06  inst_inst_num_from_inst_to_res:         0
% 3.05/1.06  inst_dismatching_checking_time:         0.
% 3.05/1.06  
% 3.05/1.06  ------ Resolution
% 3.05/1.06  
% 3.05/1.06  res_num_of_clauses:                     0
% 3.05/1.06  res_num_in_passive:                     0
% 3.05/1.06  res_num_in_active:                      0
% 3.05/1.06  res_num_of_loops:                       135
% 3.05/1.06  res_forward_subset_subsumed:            22
% 3.05/1.06  res_backward_subset_subsumed:           0
% 3.05/1.06  res_forward_subsumed:                   0
% 3.05/1.06  res_backward_subsumed:                  0
% 3.05/1.06  res_forward_subsumption_resolution:     0
% 3.05/1.06  res_backward_subsumption_resolution:    0
% 3.05/1.06  res_clause_to_clause_subsumption:       558
% 3.05/1.06  res_orphan_elimination:                 0
% 3.05/1.06  res_tautology_del:                      98
% 3.05/1.06  res_num_eq_res_simplified:              0
% 3.05/1.06  res_num_sel_changes:                    0
% 3.05/1.06  res_moves_from_active_to_pass:          0
% 3.05/1.06  
% 3.05/1.06  ------ Superposition
% 3.05/1.06  
% 3.05/1.06  sup_time_total:                         0.
% 3.05/1.06  sup_time_generating:                    0.
% 3.05/1.06  sup_time_sim_full:                      0.
% 3.05/1.06  sup_time_sim_immed:                     0.
% 3.05/1.06  
% 3.05/1.06  sup_num_of_clauses:                     161
% 3.05/1.06  sup_num_in_active:                      68
% 3.05/1.06  sup_num_in_passive:                     93
% 3.05/1.06  sup_num_of_loops:                       73
% 3.05/1.06  sup_fw_superposition:                   107
% 3.05/1.06  sup_bw_superposition:                   72
% 3.05/1.06  sup_immediate_simplified:               17
% 3.05/1.06  sup_given_eliminated:                   0
% 3.05/1.06  comparisons_done:                       0
% 3.05/1.06  comparisons_avoided:                    0
% 3.05/1.06  
% 3.05/1.06  ------ Simplifications
% 3.05/1.06  
% 3.05/1.06  
% 3.05/1.06  sim_fw_subset_subsumed:                 12
% 3.05/1.06  sim_bw_subset_subsumed:                 4
% 3.05/1.06  sim_fw_subsumed:                        5
% 3.05/1.06  sim_bw_subsumed:                        0
% 3.05/1.06  sim_fw_subsumption_res:                 0
% 3.05/1.06  sim_bw_subsumption_res:                 0
% 3.05/1.06  sim_tautology_del:                      3
% 3.05/1.06  sim_eq_tautology_del:                   0
% 3.05/1.06  sim_eq_res_simp:                        0
% 3.05/1.06  sim_fw_demodulated:                     3
% 3.05/1.06  sim_bw_demodulated:                     4
% 3.05/1.06  sim_light_normalised:                   2
% 3.05/1.06  sim_joinable_taut:                      0
% 3.05/1.06  sim_joinable_simp:                      0
% 3.05/1.06  sim_ac_normalised:                      0
% 3.05/1.06  sim_smt_subsumption:                    0
% 3.05/1.06  
%------------------------------------------------------------------------------

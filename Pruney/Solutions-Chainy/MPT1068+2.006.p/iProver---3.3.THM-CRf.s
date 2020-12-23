%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:36 EST 2020

% Result     : Theorem 7.23s
% Output     : CNFRefutation 7.23s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 610 expanded)
%              Number of clauses        :  104 ( 181 expanded)
%              Number of leaves         :   23 ( 197 expanded)
%              Depth                    :   20
%              Number of atoms          :  587 (4282 expanded)
%              Number of equality atoms :  221 (1104 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f65,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f66,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f65])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(X4,k1_funct_1(X3,sK7)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7)
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK7,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
              & k1_xboole_0 != X1
              & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k1_funct_1(sK6,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5)
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(X4,k1_funct_1(sK5,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5)
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK5,X1,X2)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5)
                  & k1_xboole_0 != sK3
                  & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4))
                  & m1_subset_1(X5,sK3) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,
    ( k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7)
    & k1_xboole_0 != sK3
    & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))
    & m1_subset_1(sK7,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f66,f79,f78,f77,f76])).

fof(f120,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f80])).

fof(f122,plain,(
    m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f80])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f124,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f80])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f86,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f63])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f118,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f80])).

fof(f117,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f80])).

fof(f119,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f80])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f116,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f80])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f68,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f67])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f68,f69])).

fof(f82,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f71])).

fof(f73,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f72,f73])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f50])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f121,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f80])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f61])).

fof(f113,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f123,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f80])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
         => ( r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
           => ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f59])).

fof(f112,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f125,plain,(
    k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_3205,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_3207,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3226,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5204,plain,
    ( r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3207,c_3226])).

cnf(c_51,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3505,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3506,plain,
    ( k1_xboole_0 = sK3
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3505])).

cnf(c_3682,plain,
    ( ~ m1_subset_1(X0,sK3)
    | r2_hidden(X0,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3869,plain,
    ( ~ m1_subset_1(sK7,sK3)
    | r2_hidden(sK7,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3682])).

cnf(c_3870,plain,
    ( m1_subset_1(sK7,sK3) != iProver_top
    | r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3869])).

cnf(c_6452,plain,
    ( r2_hidden(sK7,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5204,c_51,c_36,c_3506,c_3870])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_42,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | sK4 != X2
    | sK3 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_42])).

cnf(c_581,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK5)
    | k8_relset_1(sK3,sK4,sK5,sK4) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_580])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_583,plain,
    ( k8_relset_1(sK3,sK4,sK5,sK4) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_581,c_43,c_41])).

cnf(c_3204,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_3210,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6023,plain,
    ( k8_relset_1(sK3,sK4,sK5,X0) = k10_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_3204,c_3210])).

cnf(c_6272,plain,
    ( k10_relat_1(sK5,sK4) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_583,c_6023])).

cnf(c_44,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_45,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_2338,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3546,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2338])).

cnf(c_3547,plain,
    ( sK4 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3546])).

cnf(c_3549,plain,
    ( sK4 != k1_xboole_0
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3547])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3233,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3227,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3224,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4143,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3227,c_3224])).

cnf(c_23,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3213,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4381,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4143,c_3213])).

cnf(c_4387,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3233,c_4381])).

cnf(c_6446,plain,
    ( k10_relat_1(sK5,sK4) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6272,c_45,c_3549,c_4387])).

cnf(c_18,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3217,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6449,plain,
    ( r1_tarski(sK3,k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6446,c_3217])).

cnf(c_4145,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3204,c_3224])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_334,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_335,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_334])).

cnf(c_408,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_335])).

cnf(c_3201,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_4494,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4145,c_3201])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3220,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4979,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4494,c_3220])).

cnf(c_7201,plain,
    ( r1_tarski(sK3,k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6449,c_4979])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3229,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7206,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7201,c_3229])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3214,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9662,plain,
    ( k1_funct_1(X0,k1_funct_1(sK5,X1)) = k1_funct_1(k5_relat_1(sK5,X0),X1)
    | r2_hidden(X1,sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7206,c_3214])).

cnf(c_46,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_33691,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,k1_funct_1(sK5,X1)) = k1_funct_1(k5_relat_1(sK5,X0),X1)
    | r2_hidden(X1,sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9662,c_46,c_4979])).

cnf(c_33692,plain,
    ( k1_funct_1(X0,k1_funct_1(sK5,X1)) = k1_funct_1(k5_relat_1(sK5,X0),X1)
    | r2_hidden(X1,sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_33691])).

cnf(c_33703,plain,
    ( k1_funct_1(k5_relat_1(sK5,X0),sK7) = k1_funct_1(X0,k1_funct_1(sK5,sK7))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6452,c_33692])).

cnf(c_34586,plain,
    ( k1_funct_1(k5_relat_1(sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3205,c_33703])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_3206,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3209,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5052,plain,
    ( k1_partfun1(X0,X1,sK4,sK2,X2,sK6) = k5_relat_1(X2,sK6)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3206,c_3209])).

cnf(c_49,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_5457,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK4,sK2,X2,sK6) = k5_relat_1(X2,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5052,c_49])).

cnf(c_5458,plain,
    ( k1_partfun1(X0,X1,sK4,sK2,X2,sK6) = k5_relat_1(X2,sK6)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5457])).

cnf(c_5469,plain,
    ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3204,c_5458])).

cnf(c_3664,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK6)
    | k1_partfun1(X1,X2,sK4,sK2,X0,sK6) = k5_relat_1(X0,sK6) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_3745,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK6)
    | k1_partfun1(X0,X1,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_3664])).

cnf(c_3778,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK6)
    | k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_3745])).

cnf(c_5755,plain,
    ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5469,c_43,c_41,c_40,c_39,c_3778])).

cnf(c_37,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_3208,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_591,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
    | sK4 != X2
    | sK3 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_42])).

cnf(c_592,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(sK3,sK4,sK4,X1,sK5,X0) = k8_funct_2(sK3,sK4,X1,sK5,X0)
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_596,plain,
    ( ~ v1_funct_1(X0)
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
    | k1_partfun1(sK3,sK4,sK4,X1,sK5,X0) = k8_funct_2(sK3,sK4,X1,sK5,X0)
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_592,c_43,c_41])).

cnf(c_597,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK3,sK4,sK4,X1,sK5,X0) = k8_funct_2(sK3,sK4,X1,sK5,X0)
    | k1_xboole_0 = sK4 ),
    inference(renaming,[status(thm)],[c_596])).

cnf(c_3198,plain,
    ( k1_partfun1(sK3,sK4,sK4,X0,sK5,X1) = k8_funct_2(sK3,sK4,X0,sK5,X1)
    | k1_xboole_0 = sK4
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_597])).

cnf(c_3859,plain,
    ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k8_funct_2(sK3,sK4,sK2,sK5,sK6)
    | sK4 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3208,c_3198])).

cnf(c_3860,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK6)
    | k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k8_funct_2(sK3,sK4,sK2,sK5,sK6)
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3859])).

cnf(c_3862,plain,
    ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k8_funct_2(sK3,sK4,sK2,sK5,sK6)
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3859,c_40,c_39,c_3860])).

cnf(c_5758,plain,
    ( k8_funct_2(sK3,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6)
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5755,c_3862])).

cnf(c_8236,plain,
    ( k8_funct_2(sK3,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5758,c_45,c_3549,c_4387])).

cnf(c_35,negated_conjecture,
    ( k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_8239,plain,
    ( k1_funct_1(k5_relat_1(sK5,sK6),sK7) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_8236,c_35])).

cnf(c_4144,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3206,c_3224])).

cnf(c_4493,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4144,c_3201])).

cnf(c_4918,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4493,c_3220])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34586,c_8239,c_4918])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:13:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.23/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.23/1.49  
% 7.23/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.23/1.49  
% 7.23/1.49  ------  iProver source info
% 7.23/1.49  
% 7.23/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.23/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.23/1.49  git: non_committed_changes: false
% 7.23/1.49  git: last_make_outside_of_git: false
% 7.23/1.49  
% 7.23/1.49  ------ 
% 7.23/1.49  
% 7.23/1.49  ------ Input Options
% 7.23/1.49  
% 7.23/1.49  --out_options                           all
% 7.23/1.49  --tptp_safe_out                         true
% 7.23/1.49  --problem_path                          ""
% 7.23/1.49  --include_path                          ""
% 7.23/1.49  --clausifier                            res/vclausify_rel
% 7.23/1.49  --clausifier_options                    --mode clausify
% 7.23/1.49  --stdin                                 false
% 7.23/1.49  --stats_out                             all
% 7.23/1.49  
% 7.23/1.49  ------ General Options
% 7.23/1.49  
% 7.23/1.49  --fof                                   false
% 7.23/1.49  --time_out_real                         305.
% 7.23/1.49  --time_out_virtual                      -1.
% 7.23/1.49  --symbol_type_check                     false
% 7.23/1.49  --clausify_out                          false
% 7.23/1.49  --sig_cnt_out                           false
% 7.23/1.49  --trig_cnt_out                          false
% 7.23/1.49  --trig_cnt_out_tolerance                1.
% 7.23/1.49  --trig_cnt_out_sk_spl                   false
% 7.23/1.49  --abstr_cl_out                          false
% 7.23/1.49  
% 7.23/1.49  ------ Global Options
% 7.23/1.49  
% 7.23/1.49  --schedule                              default
% 7.23/1.49  --add_important_lit                     false
% 7.23/1.49  --prop_solver_per_cl                    1000
% 7.23/1.49  --min_unsat_core                        false
% 7.23/1.49  --soft_assumptions                      false
% 7.23/1.49  --soft_lemma_size                       3
% 7.23/1.49  --prop_impl_unit_size                   0
% 7.23/1.49  --prop_impl_unit                        []
% 7.23/1.49  --share_sel_clauses                     true
% 7.23/1.49  --reset_solvers                         false
% 7.23/1.49  --bc_imp_inh                            [conj_cone]
% 7.23/1.49  --conj_cone_tolerance                   3.
% 7.23/1.49  --extra_neg_conj                        none
% 7.23/1.49  --large_theory_mode                     true
% 7.23/1.49  --prolific_symb_bound                   200
% 7.23/1.49  --lt_threshold                          2000
% 7.23/1.49  --clause_weak_htbl                      true
% 7.23/1.49  --gc_record_bc_elim                     false
% 7.23/1.49  
% 7.23/1.49  ------ Preprocessing Options
% 7.23/1.49  
% 7.23/1.49  --preprocessing_flag                    true
% 7.23/1.49  --time_out_prep_mult                    0.1
% 7.23/1.49  --splitting_mode                        input
% 7.23/1.49  --splitting_grd                         true
% 7.23/1.49  --splitting_cvd                         false
% 7.23/1.49  --splitting_cvd_svl                     false
% 7.23/1.49  --splitting_nvd                         32
% 7.23/1.49  --sub_typing                            true
% 7.23/1.49  --prep_gs_sim                           true
% 7.23/1.49  --prep_unflatten                        true
% 7.23/1.49  --prep_res_sim                          true
% 7.23/1.49  --prep_upred                            true
% 7.23/1.49  --prep_sem_filter                       exhaustive
% 7.23/1.49  --prep_sem_filter_out                   false
% 7.23/1.49  --pred_elim                             true
% 7.23/1.49  --res_sim_input                         true
% 7.23/1.49  --eq_ax_congr_red                       true
% 7.23/1.49  --pure_diseq_elim                       true
% 7.23/1.49  --brand_transform                       false
% 7.23/1.49  --non_eq_to_eq                          false
% 7.23/1.49  --prep_def_merge                        true
% 7.23/1.49  --prep_def_merge_prop_impl              false
% 7.23/1.49  --prep_def_merge_mbd                    true
% 7.23/1.49  --prep_def_merge_tr_red                 false
% 7.23/1.49  --prep_def_merge_tr_cl                  false
% 7.23/1.49  --smt_preprocessing                     true
% 7.23/1.49  --smt_ac_axioms                         fast
% 7.23/1.49  --preprocessed_out                      false
% 7.23/1.49  --preprocessed_stats                    false
% 7.23/1.49  
% 7.23/1.49  ------ Abstraction refinement Options
% 7.23/1.49  
% 7.23/1.49  --abstr_ref                             []
% 7.23/1.49  --abstr_ref_prep                        false
% 7.23/1.49  --abstr_ref_until_sat                   false
% 7.23/1.49  --abstr_ref_sig_restrict                funpre
% 7.23/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.23/1.49  --abstr_ref_under                       []
% 7.23/1.49  
% 7.23/1.49  ------ SAT Options
% 7.23/1.49  
% 7.23/1.49  --sat_mode                              false
% 7.23/1.49  --sat_fm_restart_options                ""
% 7.23/1.49  --sat_gr_def                            false
% 7.23/1.49  --sat_epr_types                         true
% 7.23/1.49  --sat_non_cyclic_types                  false
% 7.23/1.49  --sat_finite_models                     false
% 7.23/1.49  --sat_fm_lemmas                         false
% 7.23/1.49  --sat_fm_prep                           false
% 7.23/1.49  --sat_fm_uc_incr                        true
% 7.23/1.49  --sat_out_model                         small
% 7.23/1.49  --sat_out_clauses                       false
% 7.23/1.49  
% 7.23/1.49  ------ QBF Options
% 7.23/1.49  
% 7.23/1.49  --qbf_mode                              false
% 7.23/1.49  --qbf_elim_univ                         false
% 7.23/1.49  --qbf_dom_inst                          none
% 7.23/1.49  --qbf_dom_pre_inst                      false
% 7.23/1.49  --qbf_sk_in                             false
% 7.23/1.49  --qbf_pred_elim                         true
% 7.23/1.49  --qbf_split                             512
% 7.23/1.49  
% 7.23/1.49  ------ BMC1 Options
% 7.23/1.49  
% 7.23/1.49  --bmc1_incremental                      false
% 7.23/1.49  --bmc1_axioms                           reachable_all
% 7.23/1.49  --bmc1_min_bound                        0
% 7.23/1.49  --bmc1_max_bound                        -1
% 7.23/1.49  --bmc1_max_bound_default                -1
% 7.23/1.49  --bmc1_symbol_reachability              true
% 7.23/1.49  --bmc1_property_lemmas                  false
% 7.23/1.49  --bmc1_k_induction                      false
% 7.23/1.49  --bmc1_non_equiv_states                 false
% 7.23/1.49  --bmc1_deadlock                         false
% 7.23/1.49  --bmc1_ucm                              false
% 7.23/1.49  --bmc1_add_unsat_core                   none
% 7.23/1.49  --bmc1_unsat_core_children              false
% 7.23/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.23/1.49  --bmc1_out_stat                         full
% 7.23/1.49  --bmc1_ground_init                      false
% 7.23/1.49  --bmc1_pre_inst_next_state              false
% 7.23/1.49  --bmc1_pre_inst_state                   false
% 7.23/1.49  --bmc1_pre_inst_reach_state             false
% 7.23/1.49  --bmc1_out_unsat_core                   false
% 7.23/1.49  --bmc1_aig_witness_out                  false
% 7.23/1.49  --bmc1_verbose                          false
% 7.23/1.49  --bmc1_dump_clauses_tptp                false
% 7.23/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.23/1.49  --bmc1_dump_file                        -
% 7.23/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.23/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.23/1.49  --bmc1_ucm_extend_mode                  1
% 7.23/1.49  --bmc1_ucm_init_mode                    2
% 7.23/1.49  --bmc1_ucm_cone_mode                    none
% 7.23/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.23/1.49  --bmc1_ucm_relax_model                  4
% 7.23/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.23/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.23/1.49  --bmc1_ucm_layered_model                none
% 7.23/1.49  --bmc1_ucm_max_lemma_size               10
% 7.23/1.49  
% 7.23/1.49  ------ AIG Options
% 7.23/1.49  
% 7.23/1.49  --aig_mode                              false
% 7.23/1.49  
% 7.23/1.49  ------ Instantiation Options
% 7.23/1.49  
% 7.23/1.49  --instantiation_flag                    true
% 7.23/1.49  --inst_sos_flag                         false
% 7.23/1.49  --inst_sos_phase                        true
% 7.23/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.23/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.23/1.49  --inst_lit_sel_side                     num_symb
% 7.23/1.49  --inst_solver_per_active                1400
% 7.23/1.49  --inst_solver_calls_frac                1.
% 7.23/1.49  --inst_passive_queue_type               priority_queues
% 7.23/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.23/1.49  --inst_passive_queues_freq              [25;2]
% 7.23/1.49  --inst_dismatching                      true
% 7.23/1.49  --inst_eager_unprocessed_to_passive     true
% 7.23/1.49  --inst_prop_sim_given                   true
% 7.23/1.49  --inst_prop_sim_new                     false
% 7.23/1.49  --inst_subs_new                         false
% 7.23/1.49  --inst_eq_res_simp                      false
% 7.23/1.49  --inst_subs_given                       false
% 7.23/1.49  --inst_orphan_elimination               true
% 7.23/1.49  --inst_learning_loop_flag               true
% 7.23/1.49  --inst_learning_start                   3000
% 7.23/1.49  --inst_learning_factor                  2
% 7.23/1.49  --inst_start_prop_sim_after_learn       3
% 7.23/1.49  --inst_sel_renew                        solver
% 7.23/1.49  --inst_lit_activity_flag                true
% 7.23/1.49  --inst_restr_to_given                   false
% 7.23/1.49  --inst_activity_threshold               500
% 7.23/1.49  --inst_out_proof                        true
% 7.23/1.49  
% 7.23/1.49  ------ Resolution Options
% 7.23/1.49  
% 7.23/1.49  --resolution_flag                       true
% 7.23/1.49  --res_lit_sel                           adaptive
% 7.23/1.49  --res_lit_sel_side                      none
% 7.23/1.49  --res_ordering                          kbo
% 7.23/1.49  --res_to_prop_solver                    active
% 7.23/1.49  --res_prop_simpl_new                    false
% 7.23/1.49  --res_prop_simpl_given                  true
% 7.23/1.49  --res_passive_queue_type                priority_queues
% 7.23/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.23/1.49  --res_passive_queues_freq               [15;5]
% 7.23/1.49  --res_forward_subs                      full
% 7.23/1.49  --res_backward_subs                     full
% 7.23/1.49  --res_forward_subs_resolution           true
% 7.23/1.49  --res_backward_subs_resolution          true
% 7.23/1.49  --res_orphan_elimination                true
% 7.23/1.49  --res_time_limit                        2.
% 7.23/1.49  --res_out_proof                         true
% 7.23/1.49  
% 7.23/1.49  ------ Superposition Options
% 7.23/1.49  
% 7.23/1.49  --superposition_flag                    true
% 7.23/1.49  --sup_passive_queue_type                priority_queues
% 7.23/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.23/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.23/1.49  --demod_completeness_check              fast
% 7.23/1.49  --demod_use_ground                      true
% 7.23/1.49  --sup_to_prop_solver                    passive
% 7.23/1.49  --sup_prop_simpl_new                    true
% 7.23/1.49  --sup_prop_simpl_given                  true
% 7.23/1.49  --sup_fun_splitting                     false
% 7.23/1.49  --sup_smt_interval                      50000
% 7.23/1.49  
% 7.23/1.49  ------ Superposition Simplification Setup
% 7.23/1.49  
% 7.23/1.49  --sup_indices_passive                   []
% 7.23/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.23/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.49  --sup_full_bw                           [BwDemod]
% 7.23/1.49  --sup_immed_triv                        [TrivRules]
% 7.23/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.23/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.49  --sup_immed_bw_main                     []
% 7.23/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.23/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.23/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.23/1.49  
% 7.23/1.49  ------ Combination Options
% 7.23/1.49  
% 7.23/1.49  --comb_res_mult                         3
% 7.23/1.49  --comb_sup_mult                         2
% 7.23/1.49  --comb_inst_mult                        10
% 7.23/1.49  
% 7.23/1.49  ------ Debug Options
% 7.23/1.49  
% 7.23/1.49  --dbg_backtrace                         false
% 7.23/1.49  --dbg_dump_prop_clauses                 false
% 7.23/1.49  --dbg_dump_prop_clauses_file            -
% 7.23/1.49  --dbg_out_stat                          false
% 7.23/1.49  ------ Parsing...
% 7.23/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.23/1.49  
% 7.23/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.23/1.49  
% 7.23/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.23/1.49  
% 7.23/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.23/1.49  ------ Proving...
% 7.23/1.49  ------ Problem Properties 
% 7.23/1.49  
% 7.23/1.49  
% 7.23/1.49  clauses                                 40
% 7.23/1.49  conjectures                             9
% 7.23/1.49  EPR                                     13
% 7.23/1.49  Horn                                    35
% 7.23/1.49  unary                                   11
% 7.23/1.49  binary                                  16
% 7.23/1.49  lits                                    89
% 7.23/1.49  lits eq                                 17
% 7.23/1.49  fd_pure                                 0
% 7.23/1.49  fd_pseudo                               0
% 7.23/1.49  fd_cond                                 1
% 7.23/1.49  fd_pseudo_cond                          0
% 7.23/1.49  AC symbols                              0
% 7.23/1.49  
% 7.23/1.49  ------ Schedule dynamic 5 is on 
% 7.23/1.49  
% 7.23/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.23/1.49  
% 7.23/1.49  
% 7.23/1.49  ------ 
% 7.23/1.49  Current options:
% 7.23/1.49  ------ 
% 7.23/1.49  
% 7.23/1.49  ------ Input Options
% 7.23/1.49  
% 7.23/1.49  --out_options                           all
% 7.23/1.49  --tptp_safe_out                         true
% 7.23/1.49  --problem_path                          ""
% 7.23/1.49  --include_path                          ""
% 7.23/1.49  --clausifier                            res/vclausify_rel
% 7.23/1.49  --clausifier_options                    --mode clausify
% 7.23/1.49  --stdin                                 false
% 7.23/1.49  --stats_out                             all
% 7.23/1.49  
% 7.23/1.49  ------ General Options
% 7.23/1.49  
% 7.23/1.49  --fof                                   false
% 7.23/1.49  --time_out_real                         305.
% 7.23/1.49  --time_out_virtual                      -1.
% 7.23/1.49  --symbol_type_check                     false
% 7.23/1.49  --clausify_out                          false
% 7.23/1.49  --sig_cnt_out                           false
% 7.23/1.49  --trig_cnt_out                          false
% 7.23/1.49  --trig_cnt_out_tolerance                1.
% 7.23/1.49  --trig_cnt_out_sk_spl                   false
% 7.23/1.49  --abstr_cl_out                          false
% 7.23/1.49  
% 7.23/1.49  ------ Global Options
% 7.23/1.49  
% 7.23/1.49  --schedule                              default
% 7.23/1.49  --add_important_lit                     false
% 7.23/1.49  --prop_solver_per_cl                    1000
% 7.23/1.49  --min_unsat_core                        false
% 7.23/1.49  --soft_assumptions                      false
% 7.23/1.49  --soft_lemma_size                       3
% 7.23/1.49  --prop_impl_unit_size                   0
% 7.23/1.49  --prop_impl_unit                        []
% 7.23/1.49  --share_sel_clauses                     true
% 7.23/1.49  --reset_solvers                         false
% 7.23/1.49  --bc_imp_inh                            [conj_cone]
% 7.23/1.49  --conj_cone_tolerance                   3.
% 7.23/1.49  --extra_neg_conj                        none
% 7.23/1.49  --large_theory_mode                     true
% 7.23/1.49  --prolific_symb_bound                   200
% 7.23/1.49  --lt_threshold                          2000
% 7.23/1.49  --clause_weak_htbl                      true
% 7.23/1.49  --gc_record_bc_elim                     false
% 7.23/1.49  
% 7.23/1.49  ------ Preprocessing Options
% 7.23/1.49  
% 7.23/1.49  --preprocessing_flag                    true
% 7.23/1.49  --time_out_prep_mult                    0.1
% 7.23/1.49  --splitting_mode                        input
% 7.23/1.49  --splitting_grd                         true
% 7.23/1.49  --splitting_cvd                         false
% 7.23/1.49  --splitting_cvd_svl                     false
% 7.23/1.49  --splitting_nvd                         32
% 7.23/1.49  --sub_typing                            true
% 7.23/1.49  --prep_gs_sim                           true
% 7.23/1.49  --prep_unflatten                        true
% 7.23/1.49  --prep_res_sim                          true
% 7.23/1.49  --prep_upred                            true
% 7.23/1.49  --prep_sem_filter                       exhaustive
% 7.23/1.49  --prep_sem_filter_out                   false
% 7.23/1.49  --pred_elim                             true
% 7.23/1.49  --res_sim_input                         true
% 7.23/1.49  --eq_ax_congr_red                       true
% 7.23/1.49  --pure_diseq_elim                       true
% 7.23/1.49  --brand_transform                       false
% 7.23/1.49  --non_eq_to_eq                          false
% 7.23/1.49  --prep_def_merge                        true
% 7.23/1.49  --prep_def_merge_prop_impl              false
% 7.23/1.49  --prep_def_merge_mbd                    true
% 7.23/1.49  --prep_def_merge_tr_red                 false
% 7.23/1.49  --prep_def_merge_tr_cl                  false
% 7.23/1.49  --smt_preprocessing                     true
% 7.23/1.49  --smt_ac_axioms                         fast
% 7.23/1.49  --preprocessed_out                      false
% 7.23/1.49  --preprocessed_stats                    false
% 7.23/1.49  
% 7.23/1.49  ------ Abstraction refinement Options
% 7.23/1.49  
% 7.23/1.49  --abstr_ref                             []
% 7.23/1.49  --abstr_ref_prep                        false
% 7.23/1.49  --abstr_ref_until_sat                   false
% 7.23/1.49  --abstr_ref_sig_restrict                funpre
% 7.23/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.23/1.49  --abstr_ref_under                       []
% 7.23/1.49  
% 7.23/1.49  ------ SAT Options
% 7.23/1.49  
% 7.23/1.49  --sat_mode                              false
% 7.23/1.49  --sat_fm_restart_options                ""
% 7.23/1.49  --sat_gr_def                            false
% 7.23/1.49  --sat_epr_types                         true
% 7.23/1.49  --sat_non_cyclic_types                  false
% 7.23/1.49  --sat_finite_models                     false
% 7.23/1.49  --sat_fm_lemmas                         false
% 7.23/1.49  --sat_fm_prep                           false
% 7.23/1.49  --sat_fm_uc_incr                        true
% 7.23/1.49  --sat_out_model                         small
% 7.23/1.49  --sat_out_clauses                       false
% 7.23/1.49  
% 7.23/1.49  ------ QBF Options
% 7.23/1.49  
% 7.23/1.49  --qbf_mode                              false
% 7.23/1.49  --qbf_elim_univ                         false
% 7.23/1.49  --qbf_dom_inst                          none
% 7.23/1.49  --qbf_dom_pre_inst                      false
% 7.23/1.49  --qbf_sk_in                             false
% 7.23/1.49  --qbf_pred_elim                         true
% 7.23/1.49  --qbf_split                             512
% 7.23/1.49  
% 7.23/1.49  ------ BMC1 Options
% 7.23/1.49  
% 7.23/1.49  --bmc1_incremental                      false
% 7.23/1.49  --bmc1_axioms                           reachable_all
% 7.23/1.49  --bmc1_min_bound                        0
% 7.23/1.49  --bmc1_max_bound                        -1
% 7.23/1.49  --bmc1_max_bound_default                -1
% 7.23/1.49  --bmc1_symbol_reachability              true
% 7.23/1.49  --bmc1_property_lemmas                  false
% 7.23/1.49  --bmc1_k_induction                      false
% 7.23/1.49  --bmc1_non_equiv_states                 false
% 7.23/1.49  --bmc1_deadlock                         false
% 7.23/1.49  --bmc1_ucm                              false
% 7.23/1.49  --bmc1_add_unsat_core                   none
% 7.23/1.49  --bmc1_unsat_core_children              false
% 7.23/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.23/1.49  --bmc1_out_stat                         full
% 7.23/1.49  --bmc1_ground_init                      false
% 7.23/1.49  --bmc1_pre_inst_next_state              false
% 7.23/1.49  --bmc1_pre_inst_state                   false
% 7.23/1.49  --bmc1_pre_inst_reach_state             false
% 7.23/1.49  --bmc1_out_unsat_core                   false
% 7.23/1.49  --bmc1_aig_witness_out                  false
% 7.23/1.49  --bmc1_verbose                          false
% 7.23/1.49  --bmc1_dump_clauses_tptp                false
% 7.23/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.23/1.49  --bmc1_dump_file                        -
% 7.23/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.23/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.23/1.49  --bmc1_ucm_extend_mode                  1
% 7.23/1.49  --bmc1_ucm_init_mode                    2
% 7.23/1.49  --bmc1_ucm_cone_mode                    none
% 7.23/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.23/1.49  --bmc1_ucm_relax_model                  4
% 7.23/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.23/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.23/1.49  --bmc1_ucm_layered_model                none
% 7.23/1.49  --bmc1_ucm_max_lemma_size               10
% 7.23/1.49  
% 7.23/1.49  ------ AIG Options
% 7.23/1.49  
% 7.23/1.49  --aig_mode                              false
% 7.23/1.49  
% 7.23/1.49  ------ Instantiation Options
% 7.23/1.49  
% 7.23/1.49  --instantiation_flag                    true
% 7.23/1.49  --inst_sos_flag                         false
% 7.23/1.49  --inst_sos_phase                        true
% 7.23/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.23/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.23/1.49  --inst_lit_sel_side                     none
% 7.23/1.49  --inst_solver_per_active                1400
% 7.23/1.49  --inst_solver_calls_frac                1.
% 7.23/1.49  --inst_passive_queue_type               priority_queues
% 7.23/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.23/1.49  --inst_passive_queues_freq              [25;2]
% 7.23/1.49  --inst_dismatching                      true
% 7.23/1.49  --inst_eager_unprocessed_to_passive     true
% 7.23/1.49  --inst_prop_sim_given                   true
% 7.23/1.49  --inst_prop_sim_new                     false
% 7.23/1.49  --inst_subs_new                         false
% 7.23/1.49  --inst_eq_res_simp                      false
% 7.23/1.49  --inst_subs_given                       false
% 7.23/1.49  --inst_orphan_elimination               true
% 7.23/1.49  --inst_learning_loop_flag               true
% 7.23/1.49  --inst_learning_start                   3000
% 7.23/1.49  --inst_learning_factor                  2
% 7.23/1.49  --inst_start_prop_sim_after_learn       3
% 7.23/1.49  --inst_sel_renew                        solver
% 7.23/1.49  --inst_lit_activity_flag                true
% 7.23/1.49  --inst_restr_to_given                   false
% 7.23/1.49  --inst_activity_threshold               500
% 7.23/1.49  --inst_out_proof                        true
% 7.23/1.49  
% 7.23/1.49  ------ Resolution Options
% 7.23/1.49  
% 7.23/1.49  --resolution_flag                       false
% 7.23/1.49  --res_lit_sel                           adaptive
% 7.23/1.49  --res_lit_sel_side                      none
% 7.23/1.49  --res_ordering                          kbo
% 7.23/1.49  --res_to_prop_solver                    active
% 7.23/1.49  --res_prop_simpl_new                    false
% 7.23/1.49  --res_prop_simpl_given                  true
% 7.23/1.49  --res_passive_queue_type                priority_queues
% 7.23/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.23/1.49  --res_passive_queues_freq               [15;5]
% 7.23/1.49  --res_forward_subs                      full
% 7.23/1.49  --res_backward_subs                     full
% 7.23/1.49  --res_forward_subs_resolution           true
% 7.23/1.49  --res_backward_subs_resolution          true
% 7.23/1.49  --res_orphan_elimination                true
% 7.23/1.49  --res_time_limit                        2.
% 7.23/1.49  --res_out_proof                         true
% 7.23/1.49  
% 7.23/1.49  ------ Superposition Options
% 7.23/1.49  
% 7.23/1.49  --superposition_flag                    true
% 7.23/1.49  --sup_passive_queue_type                priority_queues
% 7.23/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.23/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.23/1.49  --demod_completeness_check              fast
% 7.23/1.49  --demod_use_ground                      true
% 7.23/1.49  --sup_to_prop_solver                    passive
% 7.23/1.49  --sup_prop_simpl_new                    true
% 7.23/1.49  --sup_prop_simpl_given                  true
% 7.23/1.49  --sup_fun_splitting                     false
% 7.23/1.49  --sup_smt_interval                      50000
% 7.23/1.49  
% 7.23/1.49  ------ Superposition Simplification Setup
% 7.23/1.49  
% 7.23/1.49  --sup_indices_passive                   []
% 7.23/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.23/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.49  --sup_full_bw                           [BwDemod]
% 7.23/1.49  --sup_immed_triv                        [TrivRules]
% 7.23/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.23/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.49  --sup_immed_bw_main                     []
% 7.23/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.23/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.23/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.23/1.49  
% 7.23/1.49  ------ Combination Options
% 7.23/1.49  
% 7.23/1.49  --comb_res_mult                         3
% 7.23/1.49  --comb_sup_mult                         2
% 7.23/1.49  --comb_inst_mult                        10
% 7.23/1.49  
% 7.23/1.49  ------ Debug Options
% 7.23/1.49  
% 7.23/1.49  --dbg_backtrace                         false
% 7.23/1.49  --dbg_dump_prop_clauses                 false
% 7.23/1.49  --dbg_dump_prop_clauses_file            -
% 7.23/1.49  --dbg_out_stat                          false
% 7.23/1.49  
% 7.23/1.49  
% 7.23/1.49  
% 7.23/1.49  
% 7.23/1.49  ------ Proving...
% 7.23/1.49  
% 7.23/1.49  
% 7.23/1.49  % SZS status Theorem for theBenchmark.p
% 7.23/1.49  
% 7.23/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.23/1.49  
% 7.23/1.49  fof(f28,conjecture,(
% 7.23/1.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 7.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f29,negated_conjecture,(
% 7.23/1.49    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 7.23/1.49    inference(negated_conjecture,[],[f28])).
% 7.23/1.49  
% 7.23/1.49  fof(f65,plain,(
% 7.23/1.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 7.23/1.49    inference(ennf_transformation,[],[f29])).
% 7.23/1.49  
% 7.23/1.49  fof(f66,plain,(
% 7.23/1.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 7.23/1.49    inference(flattening,[],[f65])).
% 7.23/1.49  
% 7.23/1.49  fof(f79,plain,(
% 7.23/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(X4,k1_funct_1(X3,sK7)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK7,X1))) )),
% 7.23/1.49    introduced(choice_axiom,[])).
% 7.23/1.49  
% 7.23/1.49  fof(f78,plain,(
% 7.23/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(sK6,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6)) & m1_subset_1(X5,X1)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK6))) )),
% 7.23/1.49    introduced(choice_axiom,[])).
% 7.23/1.49  
% 7.23/1.49  fof(f77,plain,(
% 7.23/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(sK5,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 7.23/1.49    introduced(choice_axiom,[])).
% 7.23/1.49  
% 7.23/1.49  fof(f76,plain,(
% 7.23/1.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))),
% 7.23/1.49    introduced(choice_axiom,[])).
% 7.23/1.49  
% 7.23/1.49  fof(f80,plain,(
% 7.23/1.49    (((k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 7.23/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f66,f79,f78,f77,f76])).
% 7.23/1.49  
% 7.23/1.49  fof(f120,plain,(
% 7.23/1.49    v1_funct_1(sK6)),
% 7.23/1.49    inference(cnf_transformation,[],[f80])).
% 7.23/1.49  
% 7.23/1.49  fof(f122,plain,(
% 7.23/1.49    m1_subset_1(sK7,sK3)),
% 7.23/1.49    inference(cnf_transformation,[],[f80])).
% 7.23/1.49  
% 7.23/1.49  fof(f6,axiom,(
% 7.23/1.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f34,plain,(
% 7.23/1.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.23/1.49    inference(ennf_transformation,[],[f6])).
% 7.23/1.49  
% 7.23/1.49  fof(f35,plain,(
% 7.23/1.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.23/1.49    inference(flattening,[],[f34])).
% 7.23/1.49  
% 7.23/1.49  fof(f89,plain,(
% 7.23/1.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f35])).
% 7.23/1.49  
% 7.23/1.49  fof(f124,plain,(
% 7.23/1.49    k1_xboole_0 != sK3),
% 7.23/1.49    inference(cnf_transformation,[],[f80])).
% 7.23/1.49  
% 7.23/1.49  fof(f3,axiom,(
% 7.23/1.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f32,plain,(
% 7.23/1.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.23/1.49    inference(ennf_transformation,[],[f3])).
% 7.23/1.49  
% 7.23/1.49  fof(f86,plain,(
% 7.23/1.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f32])).
% 7.23/1.49  
% 7.23/1.49  fof(f27,axiom,(
% 7.23/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 7.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f63,plain,(
% 7.23/1.49    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.23/1.49    inference(ennf_transformation,[],[f27])).
% 7.23/1.49  
% 7.23/1.49  fof(f64,plain,(
% 7.23/1.49    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.23/1.49    inference(flattening,[],[f63])).
% 7.23/1.49  
% 7.23/1.49  fof(f114,plain,(
% 7.23/1.49    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f64])).
% 7.23/1.49  
% 7.23/1.49  fof(f118,plain,(
% 7.23/1.49    v1_funct_2(sK5,sK3,sK4)),
% 7.23/1.49    inference(cnf_transformation,[],[f80])).
% 7.23/1.49  
% 7.23/1.49  fof(f117,plain,(
% 7.23/1.49    v1_funct_1(sK5)),
% 7.23/1.49    inference(cnf_transformation,[],[f80])).
% 7.23/1.49  
% 7.23/1.49  fof(f119,plain,(
% 7.23/1.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 7.23/1.49    inference(cnf_transformation,[],[f80])).
% 7.23/1.49  
% 7.23/1.49  fof(f23,axiom,(
% 7.23/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 7.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f56,plain,(
% 7.23/1.49    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.23/1.49    inference(ennf_transformation,[],[f23])).
% 7.23/1.49  
% 7.23/1.49  fof(f108,plain,(
% 7.23/1.49    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.23/1.49    inference(cnf_transformation,[],[f56])).
% 7.23/1.49  
% 7.23/1.49  fof(f116,plain,(
% 7.23/1.49    ~v1_xboole_0(sK4)),
% 7.23/1.49    inference(cnf_transformation,[],[f80])).
% 7.23/1.49  
% 7.23/1.49  fof(f1,axiom,(
% 7.23/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f67,plain,(
% 7.23/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.23/1.49    inference(nnf_transformation,[],[f1])).
% 7.23/1.49  
% 7.23/1.49  fof(f68,plain,(
% 7.23/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.23/1.49    inference(rectify,[],[f67])).
% 7.23/1.49  
% 7.23/1.49  fof(f69,plain,(
% 7.23/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.23/1.49    introduced(choice_axiom,[])).
% 7.23/1.49  
% 7.23/1.49  fof(f70,plain,(
% 7.23/1.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.23/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f68,f69])).
% 7.23/1.49  
% 7.23/1.49  fof(f82,plain,(
% 7.23/1.49    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f70])).
% 7.23/1.49  
% 7.23/1.49  fof(f5,axiom,(
% 7.23/1.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f88,plain,(
% 7.23/1.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.23/1.49    inference(cnf_transformation,[],[f5])).
% 7.23/1.49  
% 7.23/1.49  fof(f7,axiom,(
% 7.23/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f75,plain,(
% 7.23/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.23/1.49    inference(nnf_transformation,[],[f7])).
% 7.23/1.49  
% 7.23/1.49  fof(f90,plain,(
% 7.23/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.23/1.49    inference(cnf_transformation,[],[f75])).
% 7.23/1.49  
% 7.23/1.49  fof(f19,axiom,(
% 7.23/1.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f52,plain,(
% 7.23/1.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.23/1.49    inference(ennf_transformation,[],[f19])).
% 7.23/1.49  
% 7.23/1.49  fof(f104,plain,(
% 7.23/1.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f52])).
% 7.23/1.49  
% 7.23/1.49  fof(f14,axiom,(
% 7.23/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 7.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f45,plain,(
% 7.23/1.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.23/1.49    inference(ennf_transformation,[],[f14])).
% 7.23/1.49  
% 7.23/1.49  fof(f99,plain,(
% 7.23/1.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f45])).
% 7.23/1.49  
% 7.23/1.49  fof(f9,axiom,(
% 7.23/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f38,plain,(
% 7.23/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.23/1.49    inference(ennf_transformation,[],[f9])).
% 7.23/1.49  
% 7.23/1.49  fof(f93,plain,(
% 7.23/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f38])).
% 7.23/1.49  
% 7.23/1.49  fof(f91,plain,(
% 7.23/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f75])).
% 7.23/1.49  
% 7.23/1.49  fof(f11,axiom,(
% 7.23/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f96,plain,(
% 7.23/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.23/1.49    inference(cnf_transformation,[],[f11])).
% 7.23/1.49  
% 7.23/1.49  fof(f2,axiom,(
% 7.23/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f31,plain,(
% 7.23/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.23/1.49    inference(ennf_transformation,[],[f2])).
% 7.23/1.49  
% 7.23/1.49  fof(f71,plain,(
% 7.23/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.23/1.49    inference(nnf_transformation,[],[f31])).
% 7.23/1.49  
% 7.23/1.49  fof(f72,plain,(
% 7.23/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.23/1.49    inference(rectify,[],[f71])).
% 7.23/1.49  
% 7.23/1.49  fof(f73,plain,(
% 7.23/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.23/1.49    introduced(choice_axiom,[])).
% 7.23/1.49  
% 7.23/1.49  fof(f74,plain,(
% 7.23/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.23/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f72,f73])).
% 7.23/1.49  
% 7.23/1.49  fof(f83,plain,(
% 7.23/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f74])).
% 7.23/1.49  
% 7.23/1.49  fof(f18,axiom,(
% 7.23/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0))))),
% 7.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f50,plain,(
% 7.23/1.49    ! [X0,X1] : (! [X2] : ((k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.23/1.49    inference(ennf_transformation,[],[f18])).
% 7.23/1.49  
% 7.23/1.49  fof(f51,plain,(
% 7.23/1.49    ! [X0,X1] : (! [X2] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.23/1.49    inference(flattening,[],[f50])).
% 7.23/1.49  
% 7.23/1.49  fof(f103,plain,(
% 7.23/1.49    ( ! [X2,X0,X1] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f51])).
% 7.23/1.49  
% 7.23/1.49  fof(f121,plain,(
% 7.23/1.49    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 7.23/1.49    inference(cnf_transformation,[],[f80])).
% 7.23/1.49  
% 7.23/1.49  fof(f26,axiom,(
% 7.23/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f61,plain,(
% 7.23/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.23/1.49    inference(ennf_transformation,[],[f26])).
% 7.23/1.49  
% 7.23/1.49  fof(f62,plain,(
% 7.23/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.23/1.49    inference(flattening,[],[f61])).
% 7.23/1.49  
% 7.23/1.49  fof(f113,plain,(
% 7.23/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f62])).
% 7.23/1.49  
% 7.23/1.49  fof(f123,plain,(
% 7.23/1.49    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))),
% 7.23/1.49    inference(cnf_transformation,[],[f80])).
% 7.23/1.49  
% 7.23/1.49  fof(f25,axiom,(
% 7.23/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 7.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f59,plain,(
% 7.23/1.49    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.23/1.49    inference(ennf_transformation,[],[f25])).
% 7.23/1.49  
% 7.23/1.49  fof(f60,plain,(
% 7.23/1.49    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.23/1.49    inference(flattening,[],[f59])).
% 7.23/1.49  
% 7.23/1.49  fof(f112,plain,(
% 7.23/1.49    ( ! [X4,X2,X0,X3,X1] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f60])).
% 7.23/1.49  
% 7.23/1.49  fof(f125,plain,(
% 7.23/1.49    k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7)),
% 7.23/1.49    inference(cnf_transformation,[],[f80])).
% 7.23/1.49  
% 7.23/1.49  cnf(c_40,negated_conjecture,
% 7.23/1.49      ( v1_funct_1(sK6) ),
% 7.23/1.49      inference(cnf_transformation,[],[f120]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3205,plain,
% 7.23/1.49      ( v1_funct_1(sK6) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_38,negated_conjecture,
% 7.23/1.49      ( m1_subset_1(sK7,sK3) ),
% 7.23/1.49      inference(cnf_transformation,[],[f122]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3207,plain,
% 7.23/1.49      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_8,plain,
% 7.23/1.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.23/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3226,plain,
% 7.23/1.49      ( m1_subset_1(X0,X1) != iProver_top
% 7.23/1.49      | r2_hidden(X0,X1) = iProver_top
% 7.23/1.49      | v1_xboole_0(X1) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5204,plain,
% 7.23/1.49      ( r2_hidden(sK7,sK3) = iProver_top
% 7.23/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_3207,c_3226]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_51,plain,
% 7.23/1.49      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_36,negated_conjecture,
% 7.23/1.49      ( k1_xboole_0 != sK3 ),
% 7.23/1.49      inference(cnf_transformation,[],[f124]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5,plain,
% 7.23/1.49      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.23/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3505,plain,
% 7.23/1.49      ( ~ v1_xboole_0(sK3) | k1_xboole_0 = sK3 ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3506,plain,
% 7.23/1.49      ( k1_xboole_0 = sK3 | v1_xboole_0(sK3) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_3505]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3682,plain,
% 7.23/1.49      ( ~ m1_subset_1(X0,sK3) | r2_hidden(X0,sK3) | v1_xboole_0(sK3) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3869,plain,
% 7.23/1.49      ( ~ m1_subset_1(sK7,sK3) | r2_hidden(sK7,sK3) | v1_xboole_0(sK3) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_3682]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3870,plain,
% 7.23/1.49      ( m1_subset_1(sK7,sK3) != iProver_top
% 7.23/1.49      | r2_hidden(sK7,sK3) = iProver_top
% 7.23/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_3869]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_6452,plain,
% 7.23/1.49      ( r2_hidden(sK7,sK3) = iProver_top ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_5204,c_51,c_36,c_3506,c_3870]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_34,plain,
% 7.23/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.23/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.23/1.49      | ~ v1_funct_1(X0)
% 7.23/1.49      | k8_relset_1(X1,X2,X0,X2) = X1
% 7.23/1.49      | k1_xboole_0 = X2 ),
% 7.23/1.49      inference(cnf_transformation,[],[f114]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_42,negated_conjecture,
% 7.23/1.49      ( v1_funct_2(sK5,sK3,sK4) ),
% 7.23/1.49      inference(cnf_transformation,[],[f118]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_580,plain,
% 7.23/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.23/1.49      | ~ v1_funct_1(X0)
% 7.23/1.49      | k8_relset_1(X1,X2,X0,X2) = X1
% 7.23/1.49      | sK4 != X2
% 7.23/1.49      | sK3 != X1
% 7.23/1.49      | sK5 != X0
% 7.23/1.49      | k1_xboole_0 = X2 ),
% 7.23/1.49      inference(resolution_lifted,[status(thm)],[c_34,c_42]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_581,plain,
% 7.23/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.23/1.49      | ~ v1_funct_1(sK5)
% 7.23/1.49      | k8_relset_1(sK3,sK4,sK5,sK4) = sK3
% 7.23/1.49      | k1_xboole_0 = sK4 ),
% 7.23/1.49      inference(unflattening,[status(thm)],[c_580]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_43,negated_conjecture,
% 7.23/1.49      ( v1_funct_1(sK5) ),
% 7.23/1.49      inference(cnf_transformation,[],[f117]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_41,negated_conjecture,
% 7.23/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 7.23/1.49      inference(cnf_transformation,[],[f119]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_583,plain,
% 7.23/1.49      ( k8_relset_1(sK3,sK4,sK5,sK4) = sK3 | k1_xboole_0 = sK4 ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_581,c_43,c_41]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3204,plain,
% 7.23/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_27,plain,
% 7.23/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.23/1.49      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 7.23/1.49      inference(cnf_transformation,[],[f108]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3210,plain,
% 7.23/1.49      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 7.23/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_6023,plain,
% 7.23/1.49      ( k8_relset_1(sK3,sK4,sK5,X0) = k10_relat_1(sK5,X0) ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_3204,c_3210]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_6272,plain,
% 7.23/1.49      ( k10_relat_1(sK5,sK4) = sK3 | sK4 = k1_xboole_0 ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_583,c_6023]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_44,negated_conjecture,
% 7.23/1.49      ( ~ v1_xboole_0(sK4) ),
% 7.23/1.49      inference(cnf_transformation,[],[f116]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_45,plain,
% 7.23/1.49      ( v1_xboole_0(sK4) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2338,plain,
% 7.23/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.23/1.49      theory(equality) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3546,plain,
% 7.23/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_2338]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3547,plain,
% 7.23/1.49      ( sK4 != X0
% 7.23/1.49      | v1_xboole_0(X0) != iProver_top
% 7.23/1.49      | v1_xboole_0(sK4) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_3546]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3549,plain,
% 7.23/1.49      ( sK4 != k1_xboole_0
% 7.23/1.49      | v1_xboole_0(sK4) = iProver_top
% 7.23/1.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_3547]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_0,plain,
% 7.23/1.49      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 7.23/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3233,plain,
% 7.23/1.49      ( r2_hidden(sK0(X0),X0) = iProver_top
% 7.23/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7,plain,
% 7.23/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.23/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3227,plain,
% 7.23/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_10,plain,
% 7.23/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.23/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3224,plain,
% 7.23/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.23/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4143,plain,
% 7.23/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_3227,c_3224]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_23,plain,
% 7.23/1.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 7.23/1.49      inference(cnf_transformation,[],[f104]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3213,plain,
% 7.23/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.23/1.49      | r2_hidden(X1,X0) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4381,plain,
% 7.23/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_4143,c_3213]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4387,plain,
% 7.23/1.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_3233,c_4381]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_6446,plain,
% 7.23/1.49      ( k10_relat_1(sK5,sK4) = sK3 ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_6272,c_45,c_3549,c_4387]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_18,plain,
% 7.23/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.23/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3217,plain,
% 7.23/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 7.23/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_6449,plain,
% 7.23/1.49      ( r1_tarski(sK3,k1_relat_1(sK5)) = iProver_top
% 7.23/1.49      | v1_relat_1(sK5) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_6446,c_3217]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4145,plain,
% 7.23/1.49      ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_3204,c_3224]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_12,plain,
% 7.23/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.23/1.49      | ~ v1_relat_1(X1)
% 7.23/1.49      | v1_relat_1(X0) ),
% 7.23/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_9,plain,
% 7.23/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.23/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_334,plain,
% 7.23/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.23/1.49      inference(prop_impl,[status(thm)],[c_9]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_335,plain,
% 7.23/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.23/1.49      inference(renaming,[status(thm)],[c_334]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_408,plain,
% 7.23/1.49      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.23/1.49      inference(bin_hyper_res,[status(thm)],[c_12,c_335]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3201,plain,
% 7.23/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.23/1.49      | v1_relat_1(X1) != iProver_top
% 7.23/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4494,plain,
% 7.23/1.49      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 7.23/1.49      | v1_relat_1(sK5) = iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_4145,c_3201]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_15,plain,
% 7.23/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.23/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3220,plain,
% 7.23/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4979,plain,
% 7.23/1.49      ( v1_relat_1(sK5) = iProver_top ),
% 7.23/1.49      inference(forward_subsumption_resolution,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_4494,c_3220]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7201,plain,
% 7.23/1.49      ( r1_tarski(sK3,k1_relat_1(sK5)) = iProver_top ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_6449,c_4979]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4,plain,
% 7.23/1.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 7.23/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3229,plain,
% 7.23/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.23/1.49      | r2_hidden(X2,X0) != iProver_top
% 7.23/1.49      | r2_hidden(X2,X1) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7206,plain,
% 7.23/1.49      ( r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
% 7.23/1.49      | r2_hidden(X0,sK3) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_7201,c_3229]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_22,plain,
% 7.23/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.23/1.49      | ~ v1_funct_1(X2)
% 7.23/1.49      | ~ v1_funct_1(X1)
% 7.23/1.49      | ~ v1_relat_1(X2)
% 7.23/1.49      | ~ v1_relat_1(X1)
% 7.23/1.49      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 7.23/1.49      inference(cnf_transformation,[],[f103]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3214,plain,
% 7.23/1.49      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 7.23/1.49      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 7.23/1.49      | v1_funct_1(X1) != iProver_top
% 7.23/1.49      | v1_funct_1(X0) != iProver_top
% 7.23/1.49      | v1_relat_1(X1) != iProver_top
% 7.23/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_9662,plain,
% 7.23/1.49      ( k1_funct_1(X0,k1_funct_1(sK5,X1)) = k1_funct_1(k5_relat_1(sK5,X0),X1)
% 7.23/1.49      | r2_hidden(X1,sK3) != iProver_top
% 7.23/1.49      | v1_funct_1(X0) != iProver_top
% 7.23/1.49      | v1_funct_1(sK5) != iProver_top
% 7.23/1.49      | v1_relat_1(X0) != iProver_top
% 7.23/1.49      | v1_relat_1(sK5) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_7206,c_3214]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_46,plain,
% 7.23/1.49      ( v1_funct_1(sK5) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_33691,plain,
% 7.23/1.49      ( v1_relat_1(X0) != iProver_top
% 7.23/1.49      | k1_funct_1(X0,k1_funct_1(sK5,X1)) = k1_funct_1(k5_relat_1(sK5,X0),X1)
% 7.23/1.49      | r2_hidden(X1,sK3) != iProver_top
% 7.23/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_9662,c_46,c_4979]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_33692,plain,
% 7.23/1.49      ( k1_funct_1(X0,k1_funct_1(sK5,X1)) = k1_funct_1(k5_relat_1(sK5,X0),X1)
% 7.23/1.49      | r2_hidden(X1,sK3) != iProver_top
% 7.23/1.49      | v1_funct_1(X0) != iProver_top
% 7.23/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.23/1.49      inference(renaming,[status(thm)],[c_33691]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_33703,plain,
% 7.23/1.49      ( k1_funct_1(k5_relat_1(sK5,X0),sK7) = k1_funct_1(X0,k1_funct_1(sK5,sK7))
% 7.23/1.49      | v1_funct_1(X0) != iProver_top
% 7.23/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_6452,c_33692]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_34586,plain,
% 7.23/1.49      ( k1_funct_1(k5_relat_1(sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
% 7.23/1.49      | v1_relat_1(sK6) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_3205,c_33703]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_39,negated_conjecture,
% 7.23/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 7.23/1.49      inference(cnf_transformation,[],[f121]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3206,plain,
% 7.23/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_32,plain,
% 7.23/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.23/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.23/1.49      | ~ v1_funct_1(X3)
% 7.23/1.49      | ~ v1_funct_1(X0)
% 7.23/1.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.23/1.49      inference(cnf_transformation,[],[f113]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3209,plain,
% 7.23/1.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.23/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.23/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.23/1.49      | v1_funct_1(X5) != iProver_top
% 7.23/1.49      | v1_funct_1(X4) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5052,plain,
% 7.23/1.49      ( k1_partfun1(X0,X1,sK4,sK2,X2,sK6) = k5_relat_1(X2,sK6)
% 7.23/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.23/1.49      | v1_funct_1(X2) != iProver_top
% 7.23/1.49      | v1_funct_1(sK6) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_3206,c_3209]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_49,plain,
% 7.23/1.49      ( v1_funct_1(sK6) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5457,plain,
% 7.23/1.49      ( v1_funct_1(X2) != iProver_top
% 7.23/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.23/1.49      | k1_partfun1(X0,X1,sK4,sK2,X2,sK6) = k5_relat_1(X2,sK6) ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_5052,c_49]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5458,plain,
% 7.23/1.49      ( k1_partfun1(X0,X1,sK4,sK2,X2,sK6) = k5_relat_1(X2,sK6)
% 7.23/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.23/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.23/1.49      inference(renaming,[status(thm)],[c_5457]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5469,plain,
% 7.23/1.49      ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6)
% 7.23/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_3204,c_5458]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3664,plain,
% 7.23/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.23/1.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 7.23/1.49      | ~ v1_funct_1(X0)
% 7.23/1.49      | ~ v1_funct_1(sK6)
% 7.23/1.49      | k1_partfun1(X1,X2,sK4,sK2,X0,sK6) = k5_relat_1(X0,sK6) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_32]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3745,plain,
% 7.23/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.23/1.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 7.23/1.49      | ~ v1_funct_1(sK5)
% 7.23/1.49      | ~ v1_funct_1(sK6)
% 7.23/1.49      | k1_partfun1(X0,X1,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_3664]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3778,plain,
% 7.23/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.23/1.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 7.23/1.49      | ~ v1_funct_1(sK5)
% 7.23/1.49      | ~ v1_funct_1(sK6)
% 7.23/1.49      | k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_3745]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5755,plain,
% 7.23/1.49      ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6) ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_5469,c_43,c_41,c_40,c_39,c_3778]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_37,negated_conjecture,
% 7.23/1.49      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
% 7.23/1.49      inference(cnf_transformation,[],[f123]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3208,plain,
% 7.23/1.49      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_31,plain,
% 7.23/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.23/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 7.23/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.23/1.49      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
% 7.23/1.49      | ~ v1_funct_1(X3)
% 7.23/1.49      | ~ v1_funct_1(X0)
% 7.23/1.49      | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
% 7.23/1.49      | k1_xboole_0 = X2 ),
% 7.23/1.49      inference(cnf_transformation,[],[f112]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_591,plain,
% 7.23/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.23/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 7.23/1.49      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
% 7.23/1.49      | ~ v1_funct_1(X0)
% 7.23/1.49      | ~ v1_funct_1(X3)
% 7.23/1.49      | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
% 7.23/1.49      | sK4 != X2
% 7.23/1.49      | sK3 != X1
% 7.23/1.49      | sK5 != X0
% 7.23/1.49      | k1_xboole_0 = X2 ),
% 7.23/1.49      inference(resolution_lifted,[status(thm)],[c_31,c_42]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_592,plain,
% 7.23/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
% 7.23/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.23/1.49      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
% 7.23/1.49      | ~ v1_funct_1(X0)
% 7.23/1.49      | ~ v1_funct_1(sK5)
% 7.23/1.49      | k1_partfun1(sK3,sK4,sK4,X1,sK5,X0) = k8_funct_2(sK3,sK4,X1,sK5,X0)
% 7.23/1.49      | k1_xboole_0 = sK4 ),
% 7.23/1.49      inference(unflattening,[status(thm)],[c_591]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_596,plain,
% 7.23/1.49      ( ~ v1_funct_1(X0)
% 7.23/1.49      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
% 7.23/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
% 7.23/1.49      | k1_partfun1(sK3,sK4,sK4,X1,sK5,X0) = k8_funct_2(sK3,sK4,X1,sK5,X0)
% 7.23/1.49      | k1_xboole_0 = sK4 ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_592,c_43,c_41]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_597,plain,
% 7.23/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
% 7.23/1.49      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
% 7.23/1.49      | ~ v1_funct_1(X0)
% 7.23/1.49      | k1_partfun1(sK3,sK4,sK4,X1,sK5,X0) = k8_funct_2(sK3,sK4,X1,sK5,X0)
% 7.23/1.49      | k1_xboole_0 = sK4 ),
% 7.23/1.49      inference(renaming,[status(thm)],[c_596]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3198,plain,
% 7.23/1.49      ( k1_partfun1(sK3,sK4,sK4,X0,sK5,X1) = k8_funct_2(sK3,sK4,X0,sK5,X1)
% 7.23/1.49      | k1_xboole_0 = sK4
% 7.23/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
% 7.23/1.49      | r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
% 7.23/1.49      | v1_funct_1(X1) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_597]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3859,plain,
% 7.23/1.49      ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k8_funct_2(sK3,sK4,sK2,sK5,sK6)
% 7.23/1.49      | sK4 = k1_xboole_0
% 7.23/1.49      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 7.23/1.49      | v1_funct_1(sK6) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_3208,c_3198]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3860,plain,
% 7.23/1.49      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 7.23/1.49      | ~ v1_funct_1(sK6)
% 7.23/1.49      | k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k8_funct_2(sK3,sK4,sK2,sK5,sK6)
% 7.23/1.49      | sK4 = k1_xboole_0 ),
% 7.23/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_3859]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3862,plain,
% 7.23/1.49      ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k8_funct_2(sK3,sK4,sK2,sK5,sK6)
% 7.23/1.49      | sK4 = k1_xboole_0 ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_3859,c_40,c_39,c_3860]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5758,plain,
% 7.23/1.49      ( k8_funct_2(sK3,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6)
% 7.23/1.49      | sK4 = k1_xboole_0 ),
% 7.23/1.49      inference(demodulation,[status(thm)],[c_5755,c_3862]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_8236,plain,
% 7.23/1.49      ( k8_funct_2(sK3,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6) ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_5758,c_45,c_3549,c_4387]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_35,negated_conjecture,
% 7.23/1.49      ( k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
% 7.23/1.49      inference(cnf_transformation,[],[f125]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_8239,plain,
% 7.23/1.49      ( k1_funct_1(k5_relat_1(sK5,sK6),sK7) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 7.23/1.49      inference(demodulation,[status(thm)],[c_8236,c_35]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4144,plain,
% 7.23/1.49      ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK2)) = iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_3206,c_3224]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4493,plain,
% 7.23/1.49      ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) != iProver_top
% 7.23/1.49      | v1_relat_1(sK6) = iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_4144,c_3201]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4918,plain,
% 7.23/1.49      ( v1_relat_1(sK6) = iProver_top ),
% 7.23/1.49      inference(forward_subsumption_resolution,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_4493,c_3220]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(contradiction,plain,
% 7.23/1.49      ( $false ),
% 7.23/1.49      inference(minisat,[status(thm)],[c_34586,c_8239,c_4918]) ).
% 7.23/1.49  
% 7.23/1.49  
% 7.23/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.23/1.49  
% 7.23/1.49  ------                               Statistics
% 7.23/1.49  
% 7.23/1.49  ------ General
% 7.23/1.49  
% 7.23/1.49  abstr_ref_over_cycles:                  0
% 7.23/1.49  abstr_ref_under_cycles:                 0
% 7.23/1.49  gc_basic_clause_elim:                   0
% 7.23/1.49  forced_gc_time:                         0
% 7.23/1.49  parsing_time:                           0.017
% 7.23/1.49  unif_index_cands_time:                  0.
% 7.23/1.49  unif_index_add_time:                    0.
% 7.23/1.49  orderings_time:                         0.
% 7.23/1.49  out_proof_time:                         0.015
% 7.23/1.49  total_time:                             0.736
% 7.23/1.49  num_of_symbols:                         62
% 7.23/1.49  num_of_terms:                           21881
% 7.23/1.49  
% 7.23/1.49  ------ Preprocessing
% 7.23/1.49  
% 7.23/1.49  num_of_splits:                          0
% 7.23/1.49  num_of_split_atoms:                     0
% 7.23/1.49  num_of_reused_defs:                     0
% 7.23/1.49  num_eq_ax_congr_red:                    48
% 7.23/1.49  num_of_sem_filtered_clauses:            1
% 7.23/1.49  num_of_subtypes:                        0
% 7.23/1.49  monotx_restored_types:                  0
% 7.23/1.49  sat_num_of_epr_types:                   0
% 7.23/1.49  sat_num_of_non_cyclic_types:            0
% 7.23/1.49  sat_guarded_non_collapsed_types:        0
% 7.23/1.49  num_pure_diseq_elim:                    0
% 7.23/1.49  simp_replaced_by:                       0
% 7.23/1.49  res_preprocessed:                       199
% 7.23/1.49  prep_upred:                             0
% 7.23/1.49  prep_unflattend:                        103
% 7.23/1.49  smt_new_axioms:                         0
% 7.23/1.49  pred_elim_cands:                        6
% 7.23/1.49  pred_elim:                              2
% 7.23/1.49  pred_elim_cl:                           2
% 7.23/1.49  pred_elim_cycles:                       4
% 7.23/1.49  merged_defs:                            8
% 7.23/1.49  merged_defs_ncl:                        0
% 7.23/1.49  bin_hyper_res:                          9
% 7.23/1.49  prep_cycles:                            4
% 7.23/1.49  pred_elim_time:                         0.036
% 7.23/1.49  splitting_time:                         0.
% 7.23/1.49  sem_filter_time:                        0.
% 7.23/1.49  monotx_time:                            0.
% 7.23/1.49  subtype_inf_time:                       0.
% 7.23/1.49  
% 7.23/1.49  ------ Problem properties
% 7.23/1.49  
% 7.23/1.49  clauses:                                40
% 7.23/1.49  conjectures:                            9
% 7.23/1.49  epr:                                    13
% 7.23/1.49  horn:                                   35
% 7.23/1.49  ground:                                 12
% 7.23/1.49  unary:                                  11
% 7.23/1.49  binary:                                 16
% 7.23/1.49  lits:                                   89
% 7.23/1.49  lits_eq:                                17
% 7.23/1.49  fd_pure:                                0
% 7.23/1.49  fd_pseudo:                              0
% 7.23/1.49  fd_cond:                                1
% 7.23/1.49  fd_pseudo_cond:                         0
% 7.23/1.49  ac_symbols:                             0
% 7.23/1.49  
% 7.23/1.49  ------ Propositional Solver
% 7.23/1.49  
% 7.23/1.49  prop_solver_calls:                      31
% 7.23/1.49  prop_fast_solver_calls:                 2256
% 7.23/1.49  smt_solver_calls:                       0
% 7.23/1.49  smt_fast_solver_calls:                  0
% 7.23/1.49  prop_num_of_clauses:                    11396
% 7.23/1.49  prop_preprocess_simplified:             19752
% 7.23/1.49  prop_fo_subsumed:                       84
% 7.23/1.49  prop_solver_time:                       0.
% 7.23/1.49  smt_solver_time:                        0.
% 7.23/1.49  smt_fast_solver_time:                   0.
% 7.23/1.49  prop_fast_solver_time:                  0.
% 7.23/1.49  prop_unsat_core_time:                   0.001
% 7.23/1.49  
% 7.23/1.49  ------ QBF
% 7.23/1.49  
% 7.23/1.49  qbf_q_res:                              0
% 7.23/1.49  qbf_num_tautologies:                    0
% 7.23/1.49  qbf_prep_cycles:                        0
% 7.23/1.49  
% 7.23/1.49  ------ BMC1
% 7.23/1.49  
% 7.23/1.49  bmc1_current_bound:                     -1
% 7.23/1.49  bmc1_last_solved_bound:                 -1
% 7.23/1.49  bmc1_unsat_core_size:                   -1
% 7.23/1.49  bmc1_unsat_core_parents_size:           -1
% 7.23/1.49  bmc1_merge_next_fun:                    0
% 7.23/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.23/1.49  
% 7.23/1.49  ------ Instantiation
% 7.23/1.49  
% 7.23/1.49  inst_num_of_clauses:                    2710
% 7.23/1.49  inst_num_in_passive:                    545
% 7.23/1.49  inst_num_in_active:                     1423
% 7.23/1.49  inst_num_in_unprocessed:                743
% 7.23/1.49  inst_num_of_loops:                      1780
% 7.23/1.49  inst_num_of_learning_restarts:          0
% 7.23/1.49  inst_num_moves_active_passive:          353
% 7.23/1.49  inst_lit_activity:                      0
% 7.23/1.49  inst_lit_activity_moves:                0
% 7.23/1.49  inst_num_tautologies:                   0
% 7.23/1.49  inst_num_prop_implied:                  0
% 7.23/1.49  inst_num_existing_simplified:           0
% 7.23/1.49  inst_num_eq_res_simplified:             0
% 7.23/1.49  inst_num_child_elim:                    0
% 7.23/1.49  inst_num_of_dismatching_blockings:      1969
% 7.23/1.49  inst_num_of_non_proper_insts:           3182
% 7.23/1.49  inst_num_of_duplicates:                 0
% 7.23/1.49  inst_inst_num_from_inst_to_res:         0
% 7.23/1.49  inst_dismatching_checking_time:         0.
% 7.23/1.49  
% 7.23/1.49  ------ Resolution
% 7.23/1.49  
% 7.23/1.49  res_num_of_clauses:                     0
% 7.23/1.49  res_num_in_passive:                     0
% 7.23/1.49  res_num_in_active:                      0
% 7.23/1.49  res_num_of_loops:                       203
% 7.23/1.49  res_forward_subset_subsumed:            207
% 7.23/1.49  res_backward_subset_subsumed:           2
% 7.23/1.49  res_forward_subsumed:                   0
% 7.23/1.49  res_backward_subsumed:                  0
% 7.23/1.49  res_forward_subsumption_resolution:     0
% 7.23/1.49  res_backward_subsumption_resolution:    0
% 7.23/1.49  res_clause_to_clause_subsumption:       3394
% 7.23/1.49  res_orphan_elimination:                 0
% 7.23/1.49  res_tautology_del:                      223
% 7.23/1.49  res_num_eq_res_simplified:              0
% 7.23/1.49  res_num_sel_changes:                    0
% 7.23/1.49  res_moves_from_active_to_pass:          0
% 7.23/1.49  
% 7.23/1.49  ------ Superposition
% 7.23/1.49  
% 7.23/1.49  sup_time_total:                         0.
% 7.23/1.49  sup_time_generating:                    0.
% 7.23/1.49  sup_time_sim_full:                      0.
% 7.23/1.49  sup_time_sim_immed:                     0.
% 7.23/1.49  
% 7.23/1.49  sup_num_of_clauses:                     1016
% 7.23/1.49  sup_num_in_active:                      333
% 7.23/1.49  sup_num_in_passive:                     683
% 7.23/1.49  sup_num_of_loops:                       354
% 7.23/1.49  sup_fw_superposition:                   740
% 7.23/1.49  sup_bw_superposition:                   655
% 7.23/1.49  sup_immediate_simplified:               284
% 7.23/1.49  sup_given_eliminated:                   5
% 7.23/1.49  comparisons_done:                       0
% 7.23/1.49  comparisons_avoided:                    111
% 7.23/1.49  
% 7.23/1.49  ------ Simplifications
% 7.23/1.49  
% 7.23/1.49  
% 7.23/1.49  sim_fw_subset_subsumed:                 102
% 7.23/1.49  sim_bw_subset_subsumed:                 7
% 7.23/1.49  sim_fw_subsumed:                        49
% 7.23/1.49  sim_bw_subsumed:                        3
% 7.23/1.49  sim_fw_subsumption_res:                 6
% 7.23/1.49  sim_bw_subsumption_res:                 0
% 7.23/1.49  sim_tautology_del:                      25
% 7.23/1.49  sim_eq_tautology_del:                   33
% 7.23/1.49  sim_eq_res_simp:                        0
% 7.23/1.49  sim_fw_demodulated:                     69
% 7.23/1.49  sim_bw_demodulated:                     21
% 7.23/1.49  sim_light_normalised:                   93
% 7.23/1.49  sim_joinable_taut:                      0
% 7.23/1.49  sim_joinable_simp:                      0
% 7.23/1.49  sim_ac_normalised:                      0
% 7.23/1.49  sim_smt_subsumption:                    0
% 7.23/1.49  
%------------------------------------------------------------------------------

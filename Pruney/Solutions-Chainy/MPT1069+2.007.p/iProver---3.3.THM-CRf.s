%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:43 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 813 expanded)
%              Number of clauses        :  122 ( 247 expanded)
%              Number of leaves         :   26 ( 253 expanded)
%              Depth                    :   20
%              Number of atoms          :  738 (5525 expanded)
%              Number of equality atoms :  286 (1546 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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
                   => ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
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
                     => ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f46])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k7_partfun1(X0,X4,k1_funct_1(X3,sK6)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK6)
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK6,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
              & k1_xboole_0 != X1
              & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k7_partfun1(X0,sK5,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK5),X5)
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK5))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
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
                ( k7_partfun1(X0,X4,k1_funct_1(sK4,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK4,X4),X5)
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK4),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
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
                  ( k7_partfun1(sK1,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5)
                  & k1_xboole_0 != sK2
                  & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4))
                  & m1_subset_1(X5,sK2) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X3,sK2,sK3)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6)
    & k1_xboole_0 != sK2
    & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    & m1_subset_1(sK6,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f47,f56,f55,f54,f53])).

fof(f95,plain,(
    m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f97,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f57])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f94,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f96,plain,(
    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f57])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f44])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f89,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f90,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f48])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f67])).

fof(f7,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f42])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f93,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f40])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f100,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f98,plain,(
    k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2713,plain,
    ( m1_subset_1(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2725,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5121,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2713,c_2725])).

cnf(c_47,plain,
    ( m1_subset_1(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2977,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2978,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2977])).

cnf(c_3087,plain,
    ( ~ m1_subset_1(X0,sK2)
    | r2_hidden(X0,sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3279,plain,
    ( ~ m1_subset_1(sK6,sK2)
    | r2_hidden(sK6,sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3087])).

cnf(c_3280,plain,
    ( m1_subset_1(sK6,sK2) != iProver_top
    | r2_hidden(sK6,sK2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3279])).

cnf(c_5269,plain,
    ( r2_hidden(sK6,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5121,c_47,c_32,c_2978,c_3280])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2712,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2721,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4320,plain,
    ( k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2712,c_2721])).

cnf(c_33,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2714,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4459,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relat_1(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4320,c_2714])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2710,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2717,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5757,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2710,c_2717])).

cnf(c_40,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_41,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_43,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_611,plain,
    ( ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | X1 != X2
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_5])).

cnf(c_612,plain,
    ( ~ r1_xboole_0(k1_xboole_0,X0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_611])).

cnf(c_613,plain,
    ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_1979,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2990,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1979])).

cnf(c_2991,plain,
    ( sK3 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2990])).

cnf(c_2993,plain,
    ( sK3 != k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2991])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2730,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2726,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3338,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_2726])).

cnf(c_4197,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2730,c_3338])).

cnf(c_6139,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5757,c_41,c_42,c_43,c_613,c_2993,c_4197])).

cnf(c_6140,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6139])).

cnf(c_6147,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK5)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4459,c_6140])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2719,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6227,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | v1_funct_2(sK4,sK2,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6147,c_2719])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2715,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4852,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,X0) = iProver_top
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2710,c_2715])).

cnf(c_5498,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top
    | v1_funct_2(sK4,sK2,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4852,c_41,c_42,c_43,c_613,c_2993,c_4197])).

cnf(c_5499,plain,
    ( v1_funct_2(sK4,sK2,X0) = iProver_top
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5498])).

cnf(c_5506,plain,
    ( v1_funct_2(sK4,sK2,k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4459,c_5499])).

cnf(c_8734,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | k1_relat_1(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6227,c_42,c_5506])).

cnf(c_8735,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8734])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_22,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_471,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_17,c_22])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_475,plain,
    ( ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_471,c_16])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(renaming,[status(thm)],[c_475])).

cnf(c_2704,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_3215,plain,
    ( k7_partfun1(sK1,sK5,X0) = k1_funct_1(sK5,X0)
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2712,c_2704])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_45,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3328,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | k7_partfun1(sK1,sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3215,c_45])).

cnf(c_3329,plain,
    ( k7_partfun1(sK1,sK5,X0) = k1_funct_1(sK5,X0)
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3328])).

cnf(c_8746,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,X0)) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
    | k1_relat_1(sK5) = k1_xboole_0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8735,c_3329])).

cnf(c_8989,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))
    | k1_relat_1(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5269,c_8746])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2720,plain,
    ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
    | k1_xboole_0 = X0
    | v1_funct_2(X3,X0,X1) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6485,plain,
    ( k1_funct_1(k8_funct_2(X0,sK3,sK1,X1,sK5),X2) = k1_funct_1(sK5,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4320,c_2720])).

cnf(c_46,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_7489,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | k1_xboole_0 = X0
    | k1_funct_1(k8_funct_2(X0,sK3,sK1,X1,sK5),X2) = k1_funct_1(sK5,k1_funct_1(X1,X2))
    | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6485,c_41,c_45,c_46])).

cnf(c_7490,plain,
    ( k1_funct_1(k8_funct_2(X0,sK3,sK1,X1,sK5),X2) = k1_funct_1(sK5,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7489])).

cnf(c_7500,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
    | sK2 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4459,c_7490])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_92,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_93,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1978,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3007,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1978])).

cnf(c_3008,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3007])).

cnf(c_7505,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7500,c_42,c_43,c_44,c_32,c_92,c_93,c_3008])).

cnf(c_7513,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(superposition,[status(thm)],[c_2713,c_7505])).

cnf(c_31,negated_conjecture,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_7779,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(demodulation,[status(thm)],[c_7513,c_31])).

cnf(c_9012,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8989,c_7779])).

cnf(c_9028,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9012,c_6147])).

cnf(c_9046,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9028,c_7])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_8457,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_8458,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8457])).

cnf(c_8460,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8458])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_265,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_266,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_265])).

cnf(c_331,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_266])).

cnf(c_5434,plain,
    ( ~ r1_tarski(sK4,X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_5435,plain,
    ( r1_tarski(sK4,X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5434])).

cnf(c_5437,plain,
    ( r1_tarski(sK4,k1_xboole_0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5435])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_15,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_201,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_15])).

cnf(c_202,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(renaming,[status(thm)],[c_201])).

cnf(c_3086,plain,
    ( ~ v1_funct_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_3398,plain,
    ( ~ v1_funct_2(X0,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3086])).

cnf(c_3605,plain,
    ( ~ v1_funct_2(sK4,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3398])).

cnf(c_3606,plain,
    ( v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3605])).

cnf(c_9118,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(grounding,[status(thm)],[c_4197:[bind(X0,$fot(k1_xboole_0))]])).

cnf(c_9119,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(grounding,[status(thm)],[c_613:[bind(X0,$fot(k1_xboole_0))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9046,c_8460,c_5437,c_9118,c_3606,c_2978,c_9119,c_32,c_44,c_43,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:23:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.34/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/0.97  
% 3.34/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.34/0.97  
% 3.34/0.97  ------  iProver source info
% 3.34/0.97  
% 3.34/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.34/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.34/0.97  git: non_committed_changes: false
% 3.34/0.97  git: last_make_outside_of_git: false
% 3.34/0.97  
% 3.34/0.97  ------ 
% 3.34/0.97  
% 3.34/0.97  ------ Input Options
% 3.34/0.97  
% 3.34/0.97  --out_options                           all
% 3.34/0.97  --tptp_safe_out                         true
% 3.34/0.97  --problem_path                          ""
% 3.34/0.97  --include_path                          ""
% 3.34/0.97  --clausifier                            res/vclausify_rel
% 3.34/0.97  --clausifier_options                    --mode clausify
% 3.34/0.97  --stdin                                 false
% 3.34/0.97  --stats_out                             all
% 3.34/0.97  
% 3.34/0.97  ------ General Options
% 3.34/0.97  
% 3.34/0.97  --fof                                   false
% 3.34/0.97  --time_out_real                         305.
% 3.34/0.97  --time_out_virtual                      -1.
% 3.34/0.97  --symbol_type_check                     false
% 3.34/0.97  --clausify_out                          false
% 3.34/0.97  --sig_cnt_out                           false
% 3.34/0.97  --trig_cnt_out                          false
% 3.34/0.97  --trig_cnt_out_tolerance                1.
% 3.34/0.97  --trig_cnt_out_sk_spl                   false
% 3.34/0.97  --abstr_cl_out                          false
% 3.34/0.97  
% 3.34/0.97  ------ Global Options
% 3.34/0.97  
% 3.34/0.97  --schedule                              default
% 3.34/0.97  --add_important_lit                     false
% 3.34/0.97  --prop_solver_per_cl                    1000
% 3.34/0.97  --min_unsat_core                        false
% 3.34/0.97  --soft_assumptions                      false
% 3.34/0.97  --soft_lemma_size                       3
% 3.34/0.97  --prop_impl_unit_size                   0
% 3.34/0.97  --prop_impl_unit                        []
% 3.34/0.97  --share_sel_clauses                     true
% 3.34/0.97  --reset_solvers                         false
% 3.34/0.97  --bc_imp_inh                            [conj_cone]
% 3.34/0.97  --conj_cone_tolerance                   3.
% 3.34/0.97  --extra_neg_conj                        none
% 3.34/0.97  --large_theory_mode                     true
% 3.34/0.97  --prolific_symb_bound                   200
% 3.34/0.97  --lt_threshold                          2000
% 3.34/0.97  --clause_weak_htbl                      true
% 3.34/0.97  --gc_record_bc_elim                     false
% 3.34/0.97  
% 3.34/0.97  ------ Preprocessing Options
% 3.34/0.97  
% 3.34/0.97  --preprocessing_flag                    true
% 3.34/0.97  --time_out_prep_mult                    0.1
% 3.34/0.97  --splitting_mode                        input
% 3.34/0.97  --splitting_grd                         true
% 3.34/0.97  --splitting_cvd                         false
% 3.34/0.97  --splitting_cvd_svl                     false
% 3.34/0.97  --splitting_nvd                         32
% 3.34/0.97  --sub_typing                            true
% 3.34/0.97  --prep_gs_sim                           true
% 3.34/0.97  --prep_unflatten                        true
% 3.34/0.97  --prep_res_sim                          true
% 3.34/0.97  --prep_upred                            true
% 3.34/0.97  --prep_sem_filter                       exhaustive
% 3.34/0.97  --prep_sem_filter_out                   false
% 3.34/0.97  --pred_elim                             true
% 3.34/0.97  --res_sim_input                         true
% 3.34/0.97  --eq_ax_congr_red                       true
% 3.34/0.97  --pure_diseq_elim                       true
% 3.34/0.97  --brand_transform                       false
% 3.34/0.97  --non_eq_to_eq                          false
% 3.34/0.97  --prep_def_merge                        true
% 3.34/0.97  --prep_def_merge_prop_impl              false
% 3.34/0.97  --prep_def_merge_mbd                    true
% 3.34/0.97  --prep_def_merge_tr_red                 false
% 3.34/0.97  --prep_def_merge_tr_cl                  false
% 3.34/0.97  --smt_preprocessing                     true
% 3.34/0.97  --smt_ac_axioms                         fast
% 3.34/0.97  --preprocessed_out                      false
% 3.34/0.97  --preprocessed_stats                    false
% 3.34/0.97  
% 3.34/0.97  ------ Abstraction refinement Options
% 3.34/0.97  
% 3.34/0.97  --abstr_ref                             []
% 3.34/0.97  --abstr_ref_prep                        false
% 3.34/0.97  --abstr_ref_until_sat                   false
% 3.34/0.97  --abstr_ref_sig_restrict                funpre
% 3.34/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/0.97  --abstr_ref_under                       []
% 3.34/0.97  
% 3.34/0.97  ------ SAT Options
% 3.34/0.97  
% 3.34/0.97  --sat_mode                              false
% 3.34/0.97  --sat_fm_restart_options                ""
% 3.34/0.97  --sat_gr_def                            false
% 3.34/0.97  --sat_epr_types                         true
% 3.34/0.97  --sat_non_cyclic_types                  false
% 3.34/0.97  --sat_finite_models                     false
% 3.34/0.97  --sat_fm_lemmas                         false
% 3.34/0.97  --sat_fm_prep                           false
% 3.34/0.97  --sat_fm_uc_incr                        true
% 3.34/0.97  --sat_out_model                         small
% 3.34/0.97  --sat_out_clauses                       false
% 3.34/0.97  
% 3.34/0.97  ------ QBF Options
% 3.34/0.97  
% 3.34/0.97  --qbf_mode                              false
% 3.34/0.97  --qbf_elim_univ                         false
% 3.34/0.97  --qbf_dom_inst                          none
% 3.34/0.97  --qbf_dom_pre_inst                      false
% 3.34/0.97  --qbf_sk_in                             false
% 3.34/0.97  --qbf_pred_elim                         true
% 3.34/0.97  --qbf_split                             512
% 3.34/0.97  
% 3.34/0.97  ------ BMC1 Options
% 3.34/0.97  
% 3.34/0.97  --bmc1_incremental                      false
% 3.34/0.97  --bmc1_axioms                           reachable_all
% 3.34/0.97  --bmc1_min_bound                        0
% 3.34/0.97  --bmc1_max_bound                        -1
% 3.34/0.97  --bmc1_max_bound_default                -1
% 3.34/0.97  --bmc1_symbol_reachability              true
% 3.34/0.97  --bmc1_property_lemmas                  false
% 3.34/0.97  --bmc1_k_induction                      false
% 3.34/0.97  --bmc1_non_equiv_states                 false
% 3.34/0.97  --bmc1_deadlock                         false
% 3.34/0.97  --bmc1_ucm                              false
% 3.34/0.97  --bmc1_add_unsat_core                   none
% 3.34/0.97  --bmc1_unsat_core_children              false
% 3.34/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/0.97  --bmc1_out_stat                         full
% 3.34/0.97  --bmc1_ground_init                      false
% 3.34/0.97  --bmc1_pre_inst_next_state              false
% 3.34/0.97  --bmc1_pre_inst_state                   false
% 3.34/0.97  --bmc1_pre_inst_reach_state             false
% 3.34/0.97  --bmc1_out_unsat_core                   false
% 3.34/0.97  --bmc1_aig_witness_out                  false
% 3.34/0.97  --bmc1_verbose                          false
% 3.34/0.97  --bmc1_dump_clauses_tptp                false
% 3.34/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.34/0.97  --bmc1_dump_file                        -
% 3.34/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.34/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.34/0.97  --bmc1_ucm_extend_mode                  1
% 3.34/0.97  --bmc1_ucm_init_mode                    2
% 3.34/0.97  --bmc1_ucm_cone_mode                    none
% 3.34/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.34/0.97  --bmc1_ucm_relax_model                  4
% 3.34/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.34/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/0.97  --bmc1_ucm_layered_model                none
% 3.34/0.97  --bmc1_ucm_max_lemma_size               10
% 3.34/0.97  
% 3.34/0.97  ------ AIG Options
% 3.34/0.97  
% 3.34/0.97  --aig_mode                              false
% 3.34/0.97  
% 3.34/0.97  ------ Instantiation Options
% 3.34/0.97  
% 3.34/0.97  --instantiation_flag                    true
% 3.34/0.97  --inst_sos_flag                         false
% 3.34/0.97  --inst_sos_phase                        true
% 3.34/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/0.97  --inst_lit_sel_side                     num_symb
% 3.34/0.97  --inst_solver_per_active                1400
% 3.34/0.97  --inst_solver_calls_frac                1.
% 3.34/0.97  --inst_passive_queue_type               priority_queues
% 3.34/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/0.97  --inst_passive_queues_freq              [25;2]
% 3.34/0.97  --inst_dismatching                      true
% 3.34/0.97  --inst_eager_unprocessed_to_passive     true
% 3.34/0.97  --inst_prop_sim_given                   true
% 3.34/0.97  --inst_prop_sim_new                     false
% 3.34/0.97  --inst_subs_new                         false
% 3.34/0.97  --inst_eq_res_simp                      false
% 3.34/0.97  --inst_subs_given                       false
% 3.34/0.97  --inst_orphan_elimination               true
% 3.34/0.97  --inst_learning_loop_flag               true
% 3.34/0.97  --inst_learning_start                   3000
% 3.34/0.97  --inst_learning_factor                  2
% 3.34/0.97  --inst_start_prop_sim_after_learn       3
% 3.34/0.97  --inst_sel_renew                        solver
% 3.34/0.97  --inst_lit_activity_flag                true
% 3.34/0.97  --inst_restr_to_given                   false
% 3.34/0.97  --inst_activity_threshold               500
% 3.34/0.97  --inst_out_proof                        true
% 3.34/0.97  
% 3.34/0.97  ------ Resolution Options
% 3.34/0.97  
% 3.34/0.97  --resolution_flag                       true
% 3.34/0.97  --res_lit_sel                           adaptive
% 3.34/0.97  --res_lit_sel_side                      none
% 3.34/0.97  --res_ordering                          kbo
% 3.34/0.97  --res_to_prop_solver                    active
% 3.34/0.97  --res_prop_simpl_new                    false
% 3.34/0.97  --res_prop_simpl_given                  true
% 3.34/0.97  --res_passive_queue_type                priority_queues
% 3.34/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/0.97  --res_passive_queues_freq               [15;5]
% 3.34/0.97  --res_forward_subs                      full
% 3.34/0.97  --res_backward_subs                     full
% 3.34/0.97  --res_forward_subs_resolution           true
% 3.34/0.97  --res_backward_subs_resolution          true
% 3.34/0.97  --res_orphan_elimination                true
% 3.34/0.97  --res_time_limit                        2.
% 3.34/0.97  --res_out_proof                         true
% 3.34/0.97  
% 3.34/0.97  ------ Superposition Options
% 3.34/0.97  
% 3.34/0.97  --superposition_flag                    true
% 3.34/0.97  --sup_passive_queue_type                priority_queues
% 3.34/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.34/0.97  --demod_completeness_check              fast
% 3.34/0.97  --demod_use_ground                      true
% 3.34/0.97  --sup_to_prop_solver                    passive
% 3.34/0.97  --sup_prop_simpl_new                    true
% 3.34/0.97  --sup_prop_simpl_given                  true
% 3.34/0.97  --sup_fun_splitting                     false
% 3.34/0.97  --sup_smt_interval                      50000
% 3.34/0.97  
% 3.34/0.97  ------ Superposition Simplification Setup
% 3.34/0.97  
% 3.34/0.97  --sup_indices_passive                   []
% 3.34/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.97  --sup_full_bw                           [BwDemod]
% 3.34/0.97  --sup_immed_triv                        [TrivRules]
% 3.34/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.97  --sup_immed_bw_main                     []
% 3.34/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.97  
% 3.34/0.97  ------ Combination Options
% 3.34/0.97  
% 3.34/0.97  --comb_res_mult                         3
% 3.34/0.97  --comb_sup_mult                         2
% 3.34/0.97  --comb_inst_mult                        10
% 3.34/0.97  
% 3.34/0.97  ------ Debug Options
% 3.34/0.97  
% 3.34/0.97  --dbg_backtrace                         false
% 3.34/0.97  --dbg_dump_prop_clauses                 false
% 3.34/0.97  --dbg_dump_prop_clauses_file            -
% 3.34/0.97  --dbg_out_stat                          false
% 3.34/0.97  ------ Parsing...
% 3.34/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.34/0.97  
% 3.34/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.34/0.97  
% 3.34/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.34/0.97  
% 3.34/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.34/0.97  ------ Proving...
% 3.34/0.97  ------ Problem Properties 
% 3.34/0.97  
% 3.34/0.97  
% 3.34/0.97  clauses                                 35
% 3.34/0.97  conjectures                             10
% 3.34/0.97  EPR                                     13
% 3.34/0.97  Horn                                    26
% 3.34/0.97  unary                                   14
% 3.34/0.97  binary                                  8
% 3.34/0.97  lits                                    92
% 3.34/0.97  lits eq                                 15
% 3.34/0.97  fd_pure                                 0
% 3.34/0.97  fd_pseudo                               0
% 3.34/0.97  fd_cond                                 6
% 3.34/0.97  fd_pseudo_cond                          0
% 3.34/0.97  AC symbols                              0
% 3.34/0.97  
% 3.34/0.97  ------ Schedule dynamic 5 is on 
% 3.34/0.97  
% 3.34/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.34/0.97  
% 3.34/0.97  
% 3.34/0.97  ------ 
% 3.34/0.97  Current options:
% 3.34/0.97  ------ 
% 3.34/0.97  
% 3.34/0.97  ------ Input Options
% 3.34/0.97  
% 3.34/0.97  --out_options                           all
% 3.34/0.97  --tptp_safe_out                         true
% 3.34/0.97  --problem_path                          ""
% 3.34/0.97  --include_path                          ""
% 3.34/0.97  --clausifier                            res/vclausify_rel
% 3.34/0.97  --clausifier_options                    --mode clausify
% 3.34/0.97  --stdin                                 false
% 3.34/0.97  --stats_out                             all
% 3.34/0.97  
% 3.34/0.97  ------ General Options
% 3.34/0.97  
% 3.34/0.97  --fof                                   false
% 3.34/0.97  --time_out_real                         305.
% 3.34/0.97  --time_out_virtual                      -1.
% 3.34/0.97  --symbol_type_check                     false
% 3.34/0.97  --clausify_out                          false
% 3.34/0.97  --sig_cnt_out                           false
% 3.34/0.97  --trig_cnt_out                          false
% 3.34/0.97  --trig_cnt_out_tolerance                1.
% 3.34/0.97  --trig_cnt_out_sk_spl                   false
% 3.34/0.97  --abstr_cl_out                          false
% 3.34/0.97  
% 3.34/0.97  ------ Global Options
% 3.34/0.97  
% 3.34/0.97  --schedule                              default
% 3.34/0.97  --add_important_lit                     false
% 3.34/0.97  --prop_solver_per_cl                    1000
% 3.34/0.97  --min_unsat_core                        false
% 3.34/0.97  --soft_assumptions                      false
% 3.34/0.97  --soft_lemma_size                       3
% 3.34/0.97  --prop_impl_unit_size                   0
% 3.34/0.97  --prop_impl_unit                        []
% 3.34/0.97  --share_sel_clauses                     true
% 3.34/0.97  --reset_solvers                         false
% 3.34/0.97  --bc_imp_inh                            [conj_cone]
% 3.34/0.97  --conj_cone_tolerance                   3.
% 3.34/0.97  --extra_neg_conj                        none
% 3.34/0.97  --large_theory_mode                     true
% 3.34/0.97  --prolific_symb_bound                   200
% 3.34/0.97  --lt_threshold                          2000
% 3.34/0.97  --clause_weak_htbl                      true
% 3.34/0.97  --gc_record_bc_elim                     false
% 3.34/0.97  
% 3.34/0.97  ------ Preprocessing Options
% 3.34/0.97  
% 3.34/0.97  --preprocessing_flag                    true
% 3.34/0.97  --time_out_prep_mult                    0.1
% 3.34/0.97  --splitting_mode                        input
% 3.34/0.97  --splitting_grd                         true
% 3.34/0.97  --splitting_cvd                         false
% 3.34/0.97  --splitting_cvd_svl                     false
% 3.34/0.97  --splitting_nvd                         32
% 3.34/0.97  --sub_typing                            true
% 3.34/0.97  --prep_gs_sim                           true
% 3.34/0.97  --prep_unflatten                        true
% 3.34/0.97  --prep_res_sim                          true
% 3.34/0.97  --prep_upred                            true
% 3.34/0.97  --prep_sem_filter                       exhaustive
% 3.34/0.97  --prep_sem_filter_out                   false
% 3.34/0.97  --pred_elim                             true
% 3.34/0.97  --res_sim_input                         true
% 3.34/0.97  --eq_ax_congr_red                       true
% 3.34/0.97  --pure_diseq_elim                       true
% 3.34/0.97  --brand_transform                       false
% 3.34/0.97  --non_eq_to_eq                          false
% 3.34/0.97  --prep_def_merge                        true
% 3.34/0.97  --prep_def_merge_prop_impl              false
% 3.34/0.97  --prep_def_merge_mbd                    true
% 3.34/0.97  --prep_def_merge_tr_red                 false
% 3.34/0.97  --prep_def_merge_tr_cl                  false
% 3.34/0.97  --smt_preprocessing                     true
% 3.34/0.97  --smt_ac_axioms                         fast
% 3.34/0.97  --preprocessed_out                      false
% 3.34/0.97  --preprocessed_stats                    false
% 3.34/0.97  
% 3.34/0.97  ------ Abstraction refinement Options
% 3.34/0.97  
% 3.34/0.97  --abstr_ref                             []
% 3.34/0.97  --abstr_ref_prep                        false
% 3.34/0.97  --abstr_ref_until_sat                   false
% 3.34/0.97  --abstr_ref_sig_restrict                funpre
% 3.34/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/0.97  --abstr_ref_under                       []
% 3.34/0.97  
% 3.34/0.97  ------ SAT Options
% 3.34/0.97  
% 3.34/0.97  --sat_mode                              false
% 3.34/0.97  --sat_fm_restart_options                ""
% 3.34/0.97  --sat_gr_def                            false
% 3.34/0.97  --sat_epr_types                         true
% 3.34/0.97  --sat_non_cyclic_types                  false
% 3.34/0.97  --sat_finite_models                     false
% 3.34/0.97  --sat_fm_lemmas                         false
% 3.34/0.97  --sat_fm_prep                           false
% 3.34/0.97  --sat_fm_uc_incr                        true
% 3.34/0.97  --sat_out_model                         small
% 3.34/0.97  --sat_out_clauses                       false
% 3.34/0.97  
% 3.34/0.97  ------ QBF Options
% 3.34/0.97  
% 3.34/0.97  --qbf_mode                              false
% 3.34/0.97  --qbf_elim_univ                         false
% 3.34/0.97  --qbf_dom_inst                          none
% 3.34/0.97  --qbf_dom_pre_inst                      false
% 3.34/0.97  --qbf_sk_in                             false
% 3.34/0.97  --qbf_pred_elim                         true
% 3.34/0.97  --qbf_split                             512
% 3.34/0.97  
% 3.34/0.97  ------ BMC1 Options
% 3.34/0.97  
% 3.34/0.97  --bmc1_incremental                      false
% 3.34/0.97  --bmc1_axioms                           reachable_all
% 3.34/0.97  --bmc1_min_bound                        0
% 3.34/0.97  --bmc1_max_bound                        -1
% 3.34/0.97  --bmc1_max_bound_default                -1
% 3.34/0.97  --bmc1_symbol_reachability              true
% 3.34/0.97  --bmc1_property_lemmas                  false
% 3.34/0.97  --bmc1_k_induction                      false
% 3.34/0.97  --bmc1_non_equiv_states                 false
% 3.34/0.97  --bmc1_deadlock                         false
% 3.34/0.97  --bmc1_ucm                              false
% 3.34/0.97  --bmc1_add_unsat_core                   none
% 3.34/0.97  --bmc1_unsat_core_children              false
% 3.34/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/0.97  --bmc1_out_stat                         full
% 3.34/0.97  --bmc1_ground_init                      false
% 3.34/0.97  --bmc1_pre_inst_next_state              false
% 3.34/0.97  --bmc1_pre_inst_state                   false
% 3.34/0.97  --bmc1_pre_inst_reach_state             false
% 3.34/0.97  --bmc1_out_unsat_core                   false
% 3.34/0.97  --bmc1_aig_witness_out                  false
% 3.34/0.97  --bmc1_verbose                          false
% 3.34/0.97  --bmc1_dump_clauses_tptp                false
% 3.34/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.34/0.97  --bmc1_dump_file                        -
% 3.34/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.34/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.34/0.97  --bmc1_ucm_extend_mode                  1
% 3.34/0.97  --bmc1_ucm_init_mode                    2
% 3.34/0.97  --bmc1_ucm_cone_mode                    none
% 3.34/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.34/0.97  --bmc1_ucm_relax_model                  4
% 3.34/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.34/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/0.97  --bmc1_ucm_layered_model                none
% 3.34/0.97  --bmc1_ucm_max_lemma_size               10
% 3.34/0.97  
% 3.34/0.97  ------ AIG Options
% 3.34/0.97  
% 3.34/0.97  --aig_mode                              false
% 3.34/0.97  
% 3.34/0.97  ------ Instantiation Options
% 3.34/0.97  
% 3.34/0.97  --instantiation_flag                    true
% 3.34/0.97  --inst_sos_flag                         false
% 3.34/0.97  --inst_sos_phase                        true
% 3.34/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/0.97  --inst_lit_sel_side                     none
% 3.34/0.97  --inst_solver_per_active                1400
% 3.34/0.97  --inst_solver_calls_frac                1.
% 3.34/0.97  --inst_passive_queue_type               priority_queues
% 3.34/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/0.97  --inst_passive_queues_freq              [25;2]
% 3.34/0.97  --inst_dismatching                      true
% 3.34/0.97  --inst_eager_unprocessed_to_passive     true
% 3.34/0.97  --inst_prop_sim_given                   true
% 3.34/0.97  --inst_prop_sim_new                     false
% 3.34/0.97  --inst_subs_new                         false
% 3.34/0.97  --inst_eq_res_simp                      false
% 3.34/0.97  --inst_subs_given                       false
% 3.34/0.97  --inst_orphan_elimination               true
% 3.34/0.97  --inst_learning_loop_flag               true
% 3.34/0.97  --inst_learning_start                   3000
% 3.34/0.97  --inst_learning_factor                  2
% 3.34/0.97  --inst_start_prop_sim_after_learn       3
% 3.34/0.97  --inst_sel_renew                        solver
% 3.34/0.97  --inst_lit_activity_flag                true
% 3.34/0.97  --inst_restr_to_given                   false
% 3.34/0.97  --inst_activity_threshold               500
% 3.34/0.97  --inst_out_proof                        true
% 3.34/0.97  
% 3.34/0.97  ------ Resolution Options
% 3.34/0.97  
% 3.34/0.97  --resolution_flag                       false
% 3.34/0.97  --res_lit_sel                           adaptive
% 3.34/0.97  --res_lit_sel_side                      none
% 3.34/0.97  --res_ordering                          kbo
% 3.34/0.97  --res_to_prop_solver                    active
% 3.34/0.97  --res_prop_simpl_new                    false
% 3.34/0.97  --res_prop_simpl_given                  true
% 3.34/0.97  --res_passive_queue_type                priority_queues
% 3.34/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/0.97  --res_passive_queues_freq               [15;5]
% 3.34/0.97  --res_forward_subs                      full
% 3.34/0.97  --res_backward_subs                     full
% 3.34/0.97  --res_forward_subs_resolution           true
% 3.34/0.97  --res_backward_subs_resolution          true
% 3.34/0.97  --res_orphan_elimination                true
% 3.34/0.97  --res_time_limit                        2.
% 3.34/0.97  --res_out_proof                         true
% 3.34/0.97  
% 3.34/0.97  ------ Superposition Options
% 3.34/0.97  
% 3.34/0.97  --superposition_flag                    true
% 3.34/0.97  --sup_passive_queue_type                priority_queues
% 3.34/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.34/0.97  --demod_completeness_check              fast
% 3.34/0.97  --demod_use_ground                      true
% 3.34/0.97  --sup_to_prop_solver                    passive
% 3.34/0.97  --sup_prop_simpl_new                    true
% 3.34/0.97  --sup_prop_simpl_given                  true
% 3.34/0.97  --sup_fun_splitting                     false
% 3.34/0.97  --sup_smt_interval                      50000
% 3.34/0.97  
% 3.34/0.97  ------ Superposition Simplification Setup
% 3.34/0.97  
% 3.34/0.97  --sup_indices_passive                   []
% 3.34/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.97  --sup_full_bw                           [BwDemod]
% 3.34/0.97  --sup_immed_triv                        [TrivRules]
% 3.34/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.97  --sup_immed_bw_main                     []
% 3.34/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.97  
% 3.34/0.97  ------ Combination Options
% 3.34/0.97  
% 3.34/0.97  --comb_res_mult                         3
% 3.34/0.97  --comb_sup_mult                         2
% 3.34/0.97  --comb_inst_mult                        10
% 3.34/0.97  
% 3.34/0.97  ------ Debug Options
% 3.34/0.97  
% 3.34/0.97  --dbg_backtrace                         false
% 3.34/0.97  --dbg_dump_prop_clauses                 false
% 3.34/0.97  --dbg_dump_prop_clauses_file            -
% 3.34/0.97  --dbg_out_stat                          false
% 3.34/0.97  
% 3.34/0.97  
% 3.34/0.97  
% 3.34/0.97  
% 3.34/0.97  ------ Proving...
% 3.34/0.97  
% 3.34/0.97  
% 3.34/0.97  % SZS status Theorem for theBenchmark.p
% 3.34/0.97  
% 3.34/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.34/0.97  
% 3.34/0.97  fof(f20,conjecture,(
% 3.34/0.97    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.34/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.97  
% 3.34/0.97  fof(f21,negated_conjecture,(
% 3.34/0.97    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.34/0.97    inference(negated_conjecture,[],[f20])).
% 3.34/0.97  
% 3.34/0.97  fof(f46,plain,(
% 3.34/0.97    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 3.34/0.97    inference(ennf_transformation,[],[f21])).
% 3.34/0.97  
% 3.34/0.97  fof(f47,plain,(
% 3.34/0.97    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 3.34/0.97    inference(flattening,[],[f46])).
% 3.34/0.97  
% 3.34/0.97  fof(f56,plain,(
% 3.34/0.97    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k7_partfun1(X0,X4,k1_funct_1(X3,sK6)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK6) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK6,X1))) )),
% 3.34/0.97    introduced(choice_axiom,[])).
% 3.34/0.97  
% 3.34/0.97  fof(f55,plain,(
% 3.34/0.97    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k7_partfun1(X0,sK5,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK5),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK5)) & m1_subset_1(X5,X1)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK5))) )),
% 3.34/0.97    introduced(choice_axiom,[])).
% 3.34/0.97  
% 3.34/0.97  fof(f54,plain,(
% 3.34/0.97    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(sK4,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK4,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK4),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 3.34/0.97    introduced(choice_axiom,[])).
% 3.34/0.97  
% 3.34/0.97  fof(f53,plain,(
% 3.34/0.97    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(sK1,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))),
% 3.34/0.97    introduced(choice_axiom,[])).
% 3.34/0.97  
% 3.34/0.97  fof(f57,plain,(
% 3.34/0.97    (((k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) & m1_subset_1(sK6,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 3.34/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f47,f56,f55,f54,f53])).
% 3.34/0.97  
% 3.34/0.97  fof(f95,plain,(
% 3.34/0.97    m1_subset_1(sK6,sK2)),
% 3.34/0.97    inference(cnf_transformation,[],[f57])).
% 3.34/0.97  
% 3.34/0.97  fof(f9,axiom,(
% 3.34/0.97    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.34/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.97  
% 3.34/0.97  fof(f30,plain,(
% 3.34/0.97    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.34/0.97    inference(ennf_transformation,[],[f9])).
% 3.34/0.97  
% 3.34/0.97  fof(f31,plain,(
% 3.34/0.97    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.34/0.97    inference(flattening,[],[f30])).
% 3.34/0.97  
% 3.34/0.97  fof(f70,plain,(
% 3.34/0.97    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.34/0.97    inference(cnf_transformation,[],[f31])).
% 3.34/0.97  
% 3.34/0.97  fof(f97,plain,(
% 3.34/0.97    k1_xboole_0 != sK2),
% 3.34/0.97    inference(cnf_transformation,[],[f57])).
% 3.34/0.97  
% 3.34/0.97  fof(f1,axiom,(
% 3.34/0.97    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.34/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.97  
% 3.34/0.97  fof(f24,plain,(
% 3.34/0.97    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.34/0.97    inference(ennf_transformation,[],[f1])).
% 3.34/0.97  
% 3.34/0.97  fof(f58,plain,(
% 3.34/0.97    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.34/0.97    inference(cnf_transformation,[],[f24])).
% 3.34/0.97  
% 3.34/0.97  fof(f94,plain,(
% 3.34/0.97    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 3.34/0.97    inference(cnf_transformation,[],[f57])).
% 3.34/0.97  
% 3.34/0.97  fof(f14,axiom,(
% 3.34/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.34/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.97  
% 3.34/0.97  fof(f35,plain,(
% 3.34/0.97    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.97    inference(ennf_transformation,[],[f14])).
% 3.34/0.97  
% 3.34/0.97  fof(f76,plain,(
% 3.34/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.97    inference(cnf_transformation,[],[f35])).
% 3.34/0.97  
% 3.34/0.97  fof(f96,plain,(
% 3.34/0.97    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))),
% 3.34/0.97    inference(cnf_transformation,[],[f57])).
% 3.34/0.97  
% 3.34/0.97  fof(f92,plain,(
% 3.34/0.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.34/0.97    inference(cnf_transformation,[],[f57])).
% 3.34/0.97  
% 3.34/0.97  fof(f19,axiom,(
% 3.34/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.34/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.97  
% 3.34/0.97  fof(f44,plain,(
% 3.34/0.97    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.34/0.97    inference(ennf_transformation,[],[f19])).
% 3.34/0.97  
% 3.34/0.97  fof(f45,plain,(
% 3.34/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.34/0.97    inference(flattening,[],[f44])).
% 3.34/0.97  
% 3.34/0.97  fof(f87,plain,(
% 3.34/0.97    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.34/0.97    inference(cnf_transformation,[],[f45])).
% 3.34/0.97  
% 3.34/0.97  fof(f89,plain,(
% 3.34/0.97    ~v1_xboole_0(sK3)),
% 3.34/0.97    inference(cnf_transformation,[],[f57])).
% 3.34/0.97  
% 3.34/0.97  fof(f90,plain,(
% 3.34/0.97    v1_funct_1(sK4)),
% 3.34/0.97    inference(cnf_transformation,[],[f57])).
% 3.34/0.97  
% 3.34/0.97  fof(f91,plain,(
% 3.34/0.97    v1_funct_2(sK4,sK2,sK3)),
% 3.34/0.97    inference(cnf_transformation,[],[f57])).
% 3.34/0.97  
% 3.34/0.97  fof(f3,axiom,(
% 3.34/0.97    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.34/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.97  
% 3.34/0.97  fof(f62,plain,(
% 3.34/0.97    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.34/0.97    inference(cnf_transformation,[],[f3])).
% 3.34/0.97  
% 3.34/0.97  fof(f4,axiom,(
% 3.34/0.97    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 3.34/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.97  
% 3.34/0.97  fof(f26,plain,(
% 3.34/0.97    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 3.34/0.97    inference(ennf_transformation,[],[f4])).
% 3.34/0.97  
% 3.34/0.97  fof(f27,plain,(
% 3.34/0.97    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 3.34/0.97    inference(flattening,[],[f26])).
% 3.34/0.97  
% 3.34/0.97  fof(f63,plain,(
% 3.34/0.97    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 3.34/0.97    inference(cnf_transformation,[],[f27])).
% 3.34/0.97  
% 3.34/0.97  fof(f2,axiom,(
% 3.34/0.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.34/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.97  
% 3.34/0.97  fof(f22,plain,(
% 3.34/0.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.34/0.97    inference(rectify,[],[f2])).
% 3.34/0.97  
% 3.34/0.97  fof(f25,plain,(
% 3.34/0.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.34/0.97    inference(ennf_transformation,[],[f22])).
% 3.34/0.97  
% 3.34/0.97  fof(f48,plain,(
% 3.34/0.97    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.34/0.97    introduced(choice_axiom,[])).
% 3.34/0.97  
% 3.34/0.97  fof(f49,plain,(
% 3.34/0.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.34/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f48])).
% 3.34/0.97  
% 3.34/0.97  fof(f59,plain,(
% 3.34/0.97    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.34/0.97    inference(cnf_transformation,[],[f49])).
% 3.34/0.97  
% 3.34/0.97  fof(f6,axiom,(
% 3.34/0.97    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.34/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.97  
% 3.34/0.97  fof(f50,plain,(
% 3.34/0.97    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.34/0.97    inference(nnf_transformation,[],[f6])).
% 3.34/0.97  
% 3.34/0.97  fof(f51,plain,(
% 3.34/0.97    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.34/0.97    inference(flattening,[],[f50])).
% 3.34/0.97  
% 3.34/0.97  fof(f67,plain,(
% 3.34/0.97    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.34/0.97    inference(cnf_transformation,[],[f51])).
% 3.34/0.97  
% 3.34/0.97  fof(f99,plain,(
% 3.34/0.97    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.34/0.97    inference(equality_resolution,[],[f67])).
% 3.34/0.97  
% 3.34/0.97  fof(f7,axiom,(
% 3.34/0.97    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 3.34/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.97  
% 3.34/0.97  fof(f68,plain,(
% 3.34/0.97    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 3.34/0.97    inference(cnf_transformation,[],[f7])).
% 3.34/0.97  
% 3.34/0.97  fof(f18,axiom,(
% 3.34/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 3.34/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.97  
% 3.34/0.97  fof(f42,plain,(
% 3.34/0.97    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.34/0.97    inference(ennf_transformation,[],[f18])).
% 3.34/0.97  
% 3.34/0.97  fof(f43,plain,(
% 3.34/0.97    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.34/0.97    inference(flattening,[],[f42])).
% 3.34/0.97  
% 3.34/0.97  fof(f82,plain,(
% 3.34/0.97    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.34/0.97    inference(cnf_transformation,[],[f43])).
% 3.34/0.97  
% 3.34/0.97  fof(f85,plain,(
% 3.34/0.97    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.34/0.97    inference(cnf_transformation,[],[f45])).
% 3.34/0.97  
% 3.34/0.97  fof(f13,axiom,(
% 3.34/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.34/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.97  
% 3.34/0.97  fof(f23,plain,(
% 3.34/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.34/0.97    inference(pure_predicate_removal,[],[f13])).
% 3.34/0.97  
% 3.34/0.97  fof(f34,plain,(
% 3.34/0.97    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.97    inference(ennf_transformation,[],[f23])).
% 3.34/0.97  
% 3.34/0.97  fof(f75,plain,(
% 3.34/0.97    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.97    inference(cnf_transformation,[],[f34])).
% 3.34/0.97  
% 3.34/0.97  fof(f16,axiom,(
% 3.34/0.97    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 3.34/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.97  
% 3.34/0.97  fof(f38,plain,(
% 3.34/0.97    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.34/0.97    inference(ennf_transformation,[],[f16])).
% 3.34/0.97  
% 3.34/0.97  fof(f39,plain,(
% 3.34/0.97    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.34/0.97    inference(flattening,[],[f38])).
% 3.34/0.97  
% 3.34/0.97  fof(f80,plain,(
% 3.34/0.97    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.34/0.97    inference(cnf_transformation,[],[f39])).
% 3.34/0.97  
% 3.34/0.97  fof(f12,axiom,(
% 3.34/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.34/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.97  
% 3.34/0.97  fof(f33,plain,(
% 3.34/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.97    inference(ennf_transformation,[],[f12])).
% 3.34/0.97  
% 3.34/0.97  fof(f74,plain,(
% 3.34/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.97    inference(cnf_transformation,[],[f33])).
% 3.34/0.97  
% 3.34/0.97  fof(f93,plain,(
% 3.34/0.97    v1_funct_1(sK5)),
% 3.34/0.97    inference(cnf_transformation,[],[f57])).
% 3.34/0.97  
% 3.34/0.97  fof(f17,axiom,(
% 3.34/0.97    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.34/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.97  
% 3.34/0.97  fof(f40,plain,(
% 3.34/0.97    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 3.34/0.97    inference(ennf_transformation,[],[f17])).
% 3.34/0.97  
% 3.34/0.97  fof(f41,plain,(
% 3.34/0.97    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 3.34/0.97    inference(flattening,[],[f40])).
% 3.34/0.97  
% 3.34/0.97  fof(f81,plain,(
% 3.34/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 3.34/0.97    inference(cnf_transformation,[],[f41])).
% 3.34/0.97  
% 3.34/0.97  fof(f65,plain,(
% 3.34/0.97    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.34/0.97    inference(cnf_transformation,[],[f51])).
% 3.34/0.97  
% 3.34/0.97  fof(f66,plain,(
% 3.34/0.97    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.34/0.97    inference(cnf_transformation,[],[f51])).
% 3.34/0.97  
% 3.34/0.97  fof(f100,plain,(
% 3.34/0.97    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.34/0.97    inference(equality_resolution,[],[f66])).
% 3.34/0.97  
% 3.34/0.97  fof(f98,plain,(
% 3.34/0.97    k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6)),
% 3.34/0.97    inference(cnf_transformation,[],[f57])).
% 3.34/0.97  
% 3.34/0.97  fof(f10,axiom,(
% 3.34/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.34/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.97  
% 3.34/0.97  fof(f52,plain,(
% 3.34/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.34/0.97    inference(nnf_transformation,[],[f10])).
% 3.34/0.97  
% 3.34/0.97  fof(f71,plain,(
% 3.34/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.34/0.97    inference(cnf_transformation,[],[f52])).
% 3.34/0.97  
% 3.34/0.97  fof(f8,axiom,(
% 3.34/0.97    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.34/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.97  
% 3.34/0.97  fof(f29,plain,(
% 3.34/0.97    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.34/0.97    inference(ennf_transformation,[],[f8])).
% 3.34/0.97  
% 3.34/0.97  fof(f69,plain,(
% 3.34/0.97    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.34/0.97    inference(cnf_transformation,[],[f29])).
% 3.34/0.97  
% 3.34/0.97  fof(f72,plain,(
% 3.34/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.34/0.97    inference(cnf_transformation,[],[f52])).
% 3.34/0.97  
% 3.34/0.97  fof(f15,axiom,(
% 3.34/0.97    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 3.34/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.97  
% 3.34/0.97  fof(f36,plain,(
% 3.34/0.97    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.34/0.97    inference(ennf_transformation,[],[f15])).
% 3.34/0.97  
% 3.34/0.97  fof(f37,plain,(
% 3.34/0.97    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.34/0.97    inference(flattening,[],[f36])).
% 3.34/0.97  
% 3.34/0.97  fof(f78,plain,(
% 3.34/0.97    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.34/0.97    inference(cnf_transformation,[],[f37])).
% 3.34/0.97  
% 3.34/0.97  fof(f11,axiom,(
% 3.34/0.97    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 3.34/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.97  
% 3.34/0.97  fof(f32,plain,(
% 3.34/0.97    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 3.34/0.97    inference(ennf_transformation,[],[f11])).
% 3.34/0.97  
% 3.34/0.97  fof(f73,plain,(
% 3.34/0.97    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 3.34/0.97    inference(cnf_transformation,[],[f32])).
% 3.34/0.97  
% 3.34/0.97  cnf(c_34,negated_conjecture,
% 3.34/0.97      ( m1_subset_1(sK6,sK2) ),
% 3.34/0.97      inference(cnf_transformation,[],[f95]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_2713,plain,
% 3.34/0.97      ( m1_subset_1(sK6,sK2) = iProver_top ),
% 3.34/0.97      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_12,plain,
% 3.34/0.97      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.34/0.97      inference(cnf_transformation,[],[f70]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_2725,plain,
% 3.34/0.97      ( m1_subset_1(X0,X1) != iProver_top
% 3.34/0.97      | r2_hidden(X0,X1) = iProver_top
% 3.34/0.97      | v1_xboole_0(X1) = iProver_top ),
% 3.34/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_5121,plain,
% 3.34/0.97      ( r2_hidden(sK6,sK2) = iProver_top
% 3.34/0.97      | v1_xboole_0(sK2) = iProver_top ),
% 3.34/0.97      inference(superposition,[status(thm)],[c_2713,c_2725]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_47,plain,
% 3.34/0.97      ( m1_subset_1(sK6,sK2) = iProver_top ),
% 3.34/0.97      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_32,negated_conjecture,
% 3.34/0.97      ( k1_xboole_0 != sK2 ),
% 3.34/0.97      inference(cnf_transformation,[],[f97]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_0,plain,
% 3.34/0.97      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.34/0.97      inference(cnf_transformation,[],[f58]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_2977,plain,
% 3.34/0.97      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 3.34/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_2978,plain,
% 3.34/0.97      ( k1_xboole_0 = sK2 | v1_xboole_0(sK2) != iProver_top ),
% 3.34/0.97      inference(predicate_to_equality,[status(thm)],[c_2977]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_3087,plain,
% 3.34/0.97      ( ~ m1_subset_1(X0,sK2) | r2_hidden(X0,sK2) | v1_xboole_0(sK2) ),
% 3.34/0.97      inference(instantiation,[status(thm)],[c_12]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_3279,plain,
% 3.34/0.97      ( ~ m1_subset_1(sK6,sK2) | r2_hidden(sK6,sK2) | v1_xboole_0(sK2) ),
% 3.34/0.97      inference(instantiation,[status(thm)],[c_3087]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_3280,plain,
% 3.34/0.97      ( m1_subset_1(sK6,sK2) != iProver_top
% 3.34/0.97      | r2_hidden(sK6,sK2) = iProver_top
% 3.34/0.97      | v1_xboole_0(sK2) = iProver_top ),
% 3.34/0.97      inference(predicate_to_equality,[status(thm)],[c_3279]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_5269,plain,
% 3.34/0.97      ( r2_hidden(sK6,sK2) = iProver_top ),
% 3.34/0.97      inference(global_propositional_subsumption,
% 3.34/0.97                [status(thm)],
% 3.34/0.97                [c_5121,c_47,c_32,c_2978,c_3280]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_35,negated_conjecture,
% 3.34/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 3.34/0.97      inference(cnf_transformation,[],[f94]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_2712,plain,
% 3.34/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 3.34/0.97      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_18,plain,
% 3.34/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.97      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.34/0.97      inference(cnf_transformation,[],[f76]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_2721,plain,
% 3.34/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.34/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.34/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_4320,plain,
% 3.34/0.97      ( k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5) ),
% 3.34/0.97      inference(superposition,[status(thm)],[c_2712,c_2721]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_33,negated_conjecture,
% 3.34/0.97      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
% 3.34/0.97      inference(cnf_transformation,[],[f96]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_2714,plain,
% 3.34/0.97      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
% 3.34/0.97      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_4459,plain,
% 3.34/0.97      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relat_1(sK5)) = iProver_top ),
% 3.34/0.97      inference(demodulation,[status(thm)],[c_4320,c_2714]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_37,negated_conjecture,
% 3.34/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.34/0.97      inference(cnf_transformation,[],[f92]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_2710,plain,
% 3.34/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.34/0.97      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_26,plain,
% 3.34/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.34/0.97      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 3.34/0.97      | ~ v1_funct_1(X0)
% 3.34/0.97      | k1_xboole_0 = X2 ),
% 3.34/0.97      inference(cnf_transformation,[],[f87]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_2717,plain,
% 3.34/0.97      ( k1_xboole_0 = X0
% 3.34/0.97      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.34/0.97      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.34/0.97      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 3.34/0.97      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 3.34/0.97      | v1_funct_1(X1) != iProver_top ),
% 3.34/0.97      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_5757,plain,
% 3.34/0.97      ( sK3 = k1_xboole_0
% 3.34/0.97      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 3.34/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.34/0.97      | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top
% 3.34/0.97      | v1_funct_1(sK4) != iProver_top ),
% 3.34/0.97      inference(superposition,[status(thm)],[c_2710,c_2717]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_40,negated_conjecture,
% 3.34/0.97      ( ~ v1_xboole_0(sK3) ),
% 3.34/0.97      inference(cnf_transformation,[],[f89]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_41,plain,
% 3.34/0.97      ( v1_xboole_0(sK3) != iProver_top ),
% 3.34/0.97      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_39,negated_conjecture,
% 3.34/0.97      ( v1_funct_1(sK4) ),
% 3.34/0.97      inference(cnf_transformation,[],[f90]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_42,plain,
% 3.34/0.97      ( v1_funct_1(sK4) = iProver_top ),
% 3.34/0.97      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_38,negated_conjecture,
% 3.34/0.97      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.34/0.97      inference(cnf_transformation,[],[f91]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_43,plain,
% 3.34/0.97      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 3.34/0.97      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_4,plain,
% 3.34/0.97      ( r1_tarski(k1_xboole_0,X0) ),
% 3.34/0.97      inference(cnf_transformation,[],[f62]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_5,plain,
% 3.34/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 3.34/0.97      inference(cnf_transformation,[],[f63]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_611,plain,
% 3.34/0.97      ( ~ r1_xboole_0(X0,X1)
% 3.34/0.97      | v1_xboole_0(X0)
% 3.34/0.97      | X1 != X2
% 3.34/0.97      | k1_xboole_0 != X0 ),
% 3.34/0.97      inference(resolution_lifted,[status(thm)],[c_4,c_5]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_612,plain,
% 3.34/0.97      ( ~ r1_xboole_0(k1_xboole_0,X0) | v1_xboole_0(k1_xboole_0) ),
% 3.34/0.97      inference(unflattening,[status(thm)],[c_611]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_613,plain,
% 3.34/0.97      ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
% 3.34/0.97      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.34/0.97      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_1979,plain,
% 3.34/0.97      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.34/0.97      theory(equality) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_2990,plain,
% 3.34/0.97      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 3.34/0.97      inference(instantiation,[status(thm)],[c_1979]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_2991,plain,
% 3.34/0.97      ( sK3 != X0
% 3.34/0.97      | v1_xboole_0(X0) != iProver_top
% 3.34/0.97      | v1_xboole_0(sK3) = iProver_top ),
% 3.34/0.97      inference(predicate_to_equality,[status(thm)],[c_2990]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_2993,plain,
% 3.34/0.97      ( sK3 != k1_xboole_0
% 3.34/0.97      | v1_xboole_0(sK3) = iProver_top
% 3.34/0.97      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.34/0.97      inference(instantiation,[status(thm)],[c_2991]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_3,plain,
% 3.34/0.97      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.34/0.97      inference(cnf_transformation,[],[f59]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_2730,plain,
% 3.34/0.97      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.34/0.97      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.34/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_7,plain,
% 3.34/0.97      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.34/0.97      inference(cnf_transformation,[],[f99]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_10,plain,
% 3.34/0.97      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 3.34/0.97      inference(cnf_transformation,[],[f68]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_2726,plain,
% 3.34/0.97      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.34/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_3338,plain,
% 3.34/0.97      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.34/0.97      inference(superposition,[status(thm)],[c_7,c_2726]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_4197,plain,
% 3.34/0.97      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 3.34/0.97      inference(superposition,[status(thm)],[c_2730,c_3338]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_6139,plain,
% 3.34/0.97      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top
% 3.34/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 3.34/0.97      inference(global_propositional_subsumption,
% 3.34/0.97                [status(thm)],
% 3.34/0.97                [c_5757,c_41,c_42,c_43,c_613,c_2993,c_4197]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_6140,plain,
% 3.34/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.34/0.97      | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top ),
% 3.34/0.97      inference(renaming,[status(thm)],[c_6139]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_6147,plain,
% 3.34/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK5)))) = iProver_top ),
% 3.34/0.97      inference(superposition,[status(thm)],[c_4459,c_6140]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_24,plain,
% 3.34/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.97      | ~ r2_hidden(X3,X1)
% 3.34/0.97      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.34/0.97      | ~ v1_funct_1(X0)
% 3.34/0.97      | k1_xboole_0 = X2 ),
% 3.34/0.97      inference(cnf_transformation,[],[f82]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_2719,plain,
% 3.34/0.97      ( k1_xboole_0 = X0
% 3.34/0.97      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.34/0.97      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.34/0.97      | r2_hidden(X3,X2) != iProver_top
% 3.34/0.97      | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
% 3.34/0.97      | v1_funct_1(X1) != iProver_top ),
% 3.34/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_6227,plain,
% 3.34/0.97      ( k1_relat_1(sK5) = k1_xboole_0
% 3.34/0.97      | v1_funct_2(sK4,sK2,k1_relat_1(sK5)) != iProver_top
% 3.34/0.97      | r2_hidden(X0,sK2) != iProver_top
% 3.34/0.97      | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top
% 3.34/0.97      | v1_funct_1(sK4) != iProver_top ),
% 3.34/0.97      inference(superposition,[status(thm)],[c_6147,c_2719]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_28,plain,
% 3.34/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.97      | v1_funct_2(X0,X1,X3)
% 3.34/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.97      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 3.34/0.97      | ~ v1_funct_1(X0)
% 3.34/0.97      | k1_xboole_0 = X2 ),
% 3.34/0.97      inference(cnf_transformation,[],[f85]) ).
% 3.34/0.97  
% 3.34/0.97  cnf(c_2715,plain,
% 3.34/0.97      ( k1_xboole_0 = X0
% 3.34/0.98      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.34/0.98      | v1_funct_2(X1,X2,X3) = iProver_top
% 3.34/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.34/0.98      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 3.34/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4852,plain,
% 3.34/0.98      ( sK3 = k1_xboole_0
% 3.34/0.98      | v1_funct_2(sK4,sK2,X0) = iProver_top
% 3.34/0.98      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 3.34/0.98      | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top
% 3.34/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_2710,c_2715]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5498,plain,
% 3.34/0.98      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top
% 3.34/0.98      | v1_funct_2(sK4,sK2,X0) = iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_4852,c_41,c_42,c_43,c_613,c_2993,c_4197]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5499,plain,
% 3.34/0.98      ( v1_funct_2(sK4,sK2,X0) = iProver_top
% 3.34/0.98      | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_5498]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5506,plain,
% 3.34/0.98      ( v1_funct_2(sK4,sK2,k1_relat_1(sK5)) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_4459,c_5499]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8734,plain,
% 3.34/0.98      ( r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top
% 3.34/0.98      | r2_hidden(X0,sK2) != iProver_top
% 3.34/0.98      | k1_relat_1(sK5) = k1_xboole_0 ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_6227,c_42,c_5506]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8735,plain,
% 3.34/0.98      ( k1_relat_1(sK5) = k1_xboole_0
% 3.34/0.98      | r2_hidden(X0,sK2) != iProver_top
% 3.34/0.98      | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_8734]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_17,plain,
% 3.34/0.98      ( v5_relat_1(X0,X1)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.34/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_22,plain,
% 3.34/0.98      ( ~ v5_relat_1(X0,X1)
% 3.34/0.98      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.34/0.98      | ~ v1_relat_1(X0)
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.34/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_471,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.34/0.98      | ~ v1_relat_1(X0)
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.34/0.98      inference(resolution,[status(thm)],[c_17,c_22]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_16,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | v1_relat_1(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_475,plain,
% 3.34/0.98      ( ~ r2_hidden(X3,k1_relat_1(X0))
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_471,c_16]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_476,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_475]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2704,plain,
% 3.34/0.98      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 3.34/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 3.34/0.98      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 3.34/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3215,plain,
% 3.34/0.98      ( k7_partfun1(sK1,sK5,X0) = k1_funct_1(sK5,X0)
% 3.34/0.98      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.34/0.98      | v1_funct_1(sK5) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_2712,c_2704]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_36,negated_conjecture,
% 3.34/0.98      ( v1_funct_1(sK5) ),
% 3.34/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_45,plain,
% 3.34/0.98      ( v1_funct_1(sK5) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3328,plain,
% 3.34/0.98      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.34/0.98      | k7_partfun1(sK1,sK5,X0) = k1_funct_1(sK5,X0) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_3215,c_45]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3329,plain,
% 3.34/0.98      ( k7_partfun1(sK1,sK5,X0) = k1_funct_1(sK5,X0)
% 3.34/0.98      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_3328]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8746,plain,
% 3.34/0.98      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,X0)) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
% 3.34/0.98      | k1_relat_1(sK5) = k1_xboole_0
% 3.34/0.98      | r2_hidden(X0,sK2) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_8735,c_3329]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8989,plain,
% 3.34/0.98      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))
% 3.34/0.98      | k1_relat_1(sK5) = k1_xboole_0 ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_5269,c_8746]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_23,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.98      | ~ m1_subset_1(X3,X1)
% 3.34/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 3.34/0.98      | ~ v1_funct_1(X4)
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | v1_xboole_0(X2)
% 3.34/0.98      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 3.34/0.98      | k1_xboole_0 = X1 ),
% 3.34/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2720,plain,
% 3.34/0.98      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 3.34/0.98      | k1_xboole_0 = X0
% 3.34/0.98      | v1_funct_2(X3,X0,X1) != iProver_top
% 3.34/0.98      | m1_subset_1(X5,X0) != iProver_top
% 3.34/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.34/0.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.34/0.98      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 3.34/0.98      | v1_funct_1(X3) != iProver_top
% 3.34/0.98      | v1_funct_1(X4) != iProver_top
% 3.34/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6485,plain,
% 3.34/0.98      ( k1_funct_1(k8_funct_2(X0,sK3,sK1,X1,sK5),X2) = k1_funct_1(sK5,k1_funct_1(X1,X2))
% 3.34/0.98      | k1_xboole_0 = X0
% 3.34/0.98      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.34/0.98      | m1_subset_1(X2,X0) != iProver_top
% 3.34/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.34/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 3.34/0.98      | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
% 3.34/0.98      | v1_funct_1(X1) != iProver_top
% 3.34/0.98      | v1_funct_1(sK5) != iProver_top
% 3.34/0.98      | v1_xboole_0(sK3) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_4320,c_2720]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_46,plain,
% 3.34/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7489,plain,
% 3.34/0.98      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.34/0.98      | m1_subset_1(X2,X0) != iProver_top
% 3.34/0.98      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.34/0.98      | k1_xboole_0 = X0
% 3.34/0.98      | k1_funct_1(k8_funct_2(X0,sK3,sK1,X1,sK5),X2) = k1_funct_1(sK5,k1_funct_1(X1,X2))
% 3.34/0.98      | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
% 3.34/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_6485,c_41,c_45,c_46]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7490,plain,
% 3.34/0.98      ( k1_funct_1(k8_funct_2(X0,sK3,sK1,X1,sK5),X2) = k1_funct_1(sK5,k1_funct_1(X1,X2))
% 3.34/0.98      | k1_xboole_0 = X0
% 3.34/0.98      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.34/0.98      | m1_subset_1(X2,X0) != iProver_top
% 3.34/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.34/0.98      | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
% 3.34/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_7489]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7500,plain,
% 3.34/0.98      ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
% 3.34/0.98      | sK2 = k1_xboole_0
% 3.34/0.98      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 3.34/0.98      | m1_subset_1(X0,sK2) != iProver_top
% 3.34/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.34/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_4459,c_7490]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_44,plain,
% 3.34/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_9,plain,
% 3.34/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.34/0.98      | k1_xboole_0 = X0
% 3.34/0.98      | k1_xboole_0 = X1 ),
% 3.34/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_92,plain,
% 3.34/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.34/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8,plain,
% 3.34/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.34/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_93,plain,
% 3.34/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1978,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3007,plain,
% 3.34/0.98      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_1978]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3008,plain,
% 3.34/0.98      ( sK2 != k1_xboole_0
% 3.34/0.98      | k1_xboole_0 = sK2
% 3.34/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_3007]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7505,plain,
% 3.34/0.98      ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
% 3.34/0.98      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_7500,c_42,c_43,c_44,c_32,c_92,c_93,c_3008]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7513,plain,
% 3.34/0.98      ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_2713,c_7505]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_31,negated_conjecture,
% 3.34/0.98      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
% 3.34/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7779,plain,
% 3.34/0.98      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_7513,c_31]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_9012,plain,
% 3.34/0.98      ( k1_relat_1(sK5) = k1_xboole_0 ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_8989,c_7779]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_9028,plain,
% 3.34/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_9012,c_6147]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_9046,plain,
% 3.34/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_9028,c_7]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_14,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.34/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8457,plain,
% 3.34/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) | r1_tarski(sK4,X0) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8458,plain,
% 3.34/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.34/0.98      | r1_tarski(sK4,X0) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_8457]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8460,plain,
% 3.34/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.34/0.98      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_8458]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_11,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.34/0.98      | ~ v1_xboole_0(X1)
% 3.34/0.98      | v1_xboole_0(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_13,plain,
% 3.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.34/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_265,plain,
% 3.34/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.34/0.98      inference(prop_impl,[status(thm)],[c_13]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_266,plain,
% 3.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_265]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_331,plain,
% 3.34/0.98      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.34/0.98      inference(bin_hyper_res,[status(thm)],[c_11,c_266]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5434,plain,
% 3.34/0.98      ( ~ r1_tarski(sK4,X0) | ~ v1_xboole_0(X0) | v1_xboole_0(sK4) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_331]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5435,plain,
% 3.34/0.98      ( r1_tarski(sK4,X0) != iProver_top
% 3.34/0.98      | v1_xboole_0(X0) != iProver_top
% 3.34/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_5434]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5437,plain,
% 3.34/0.98      ( r1_tarski(sK4,k1_xboole_0) != iProver_top
% 3.34/0.98      | v1_xboole_0(sK4) = iProver_top
% 3.34/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_5435]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_20,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | ~ v1_xboole_0(X0)
% 3.34/0.98      | v1_xboole_0(X1)
% 3.34/0.98      | v1_xboole_0(X2) ),
% 3.34/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_15,plain,
% 3.34/0.98      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_201,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_funct_2(X0,X1,X2)
% 3.34/0.98      | ~ v1_xboole_0(X0)
% 3.34/0.98      | v1_xboole_0(X1)
% 3.34/0.98      | v1_xboole_0(X2) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_20,c_15]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_202,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_xboole_0(X0)
% 3.34/0.98      | v1_xboole_0(X1)
% 3.34/0.98      | v1_xboole_0(X2) ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_201]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3086,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,sK2,X1)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 3.34/0.98      | ~ v1_xboole_0(X0)
% 3.34/0.98      | v1_xboole_0(X1)
% 3.34/0.98      | v1_xboole_0(sK2) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_202]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3398,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,sK2,sK3)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.34/0.98      | ~ v1_xboole_0(X0)
% 3.34/0.98      | v1_xboole_0(sK3)
% 3.34/0.98      | v1_xboole_0(sK2) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_3086]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3605,plain,
% 3.34/0.98      ( ~ v1_funct_2(sK4,sK2,sK3)
% 3.34/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.34/0.98      | v1_xboole_0(sK3)
% 3.34/0.98      | v1_xboole_0(sK2)
% 3.34/0.98      | ~ v1_xboole_0(sK4) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_3398]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3606,plain,
% 3.34/0.98      ( v1_funct_2(sK4,sK2,sK3) != iProver_top
% 3.34/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.34/0.98      | v1_xboole_0(sK3) = iProver_top
% 3.34/0.98      | v1_xboole_0(sK2) = iProver_top
% 3.34/0.98      | v1_xboole_0(sK4) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_3605]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_9118,plain,
% 3.34/0.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.34/0.98      inference(grounding,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_4197:[bind(X0,$fot(k1_xboole_0))]]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_9119,plain,
% 3.34/0.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 3.34/0.98      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.34/0.98      inference(grounding,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_613:[bind(X0,$fot(k1_xboole_0))]]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(contradiction,plain,
% 3.34/0.98      ( $false ),
% 3.34/0.98      inference(minisat,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_9046,c_8460,c_5437,c_9118,c_3606,c_2978,c_9119,c_32,
% 3.34/0.98                 c_44,c_43,c_41]) ).
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  ------                               Statistics
% 3.34/0.98  
% 3.34/0.98  ------ General
% 3.34/0.98  
% 3.34/0.98  abstr_ref_over_cycles:                  0
% 3.34/0.98  abstr_ref_under_cycles:                 0
% 3.34/0.98  gc_basic_clause_elim:                   0
% 3.34/0.98  forced_gc_time:                         0
% 3.34/0.98  parsing_time:                           0.01
% 3.34/0.98  unif_index_cands_time:                  0.
% 3.34/0.98  unif_index_add_time:                    0.
% 3.34/0.98  orderings_time:                         0.
% 3.34/0.98  out_proof_time:                         0.018
% 3.34/0.98  total_time:                             0.39
% 3.34/0.98  num_of_symbols:                         56
% 3.34/0.98  num_of_terms:                           14222
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing
% 3.34/0.98  
% 3.34/0.98  num_of_splits:                          0
% 3.34/0.98  num_of_split_atoms:                     0
% 3.34/0.98  num_of_reused_defs:                     0
% 3.34/0.98  num_eq_ax_congr_red:                    18
% 3.34/0.98  num_of_sem_filtered_clauses:            1
% 3.34/0.98  num_of_subtypes:                        0
% 3.34/0.98  monotx_restored_types:                  0
% 3.34/0.98  sat_num_of_epr_types:                   0
% 3.34/0.98  sat_num_of_non_cyclic_types:            0
% 3.34/0.98  sat_guarded_non_collapsed_types:        0
% 3.34/0.98  num_pure_diseq_elim:                    0
% 3.34/0.98  simp_replaced_by:                       0
% 3.34/0.98  res_preprocessed:                       173
% 3.34/0.98  prep_upred:                             0
% 3.34/0.98  prep_unflattend:                        70
% 3.34/0.98  smt_new_axioms:                         0
% 3.34/0.98  pred_elim_cands:                        7
% 3.34/0.98  pred_elim:                              2
% 3.34/0.98  pred_elim_cl:                           2
% 3.34/0.98  pred_elim_cycles:                       7
% 3.34/0.98  merged_defs:                            8
% 3.34/0.98  merged_defs_ncl:                        0
% 3.34/0.98  bin_hyper_res:                          9
% 3.34/0.98  prep_cycles:                            4
% 3.34/0.98  pred_elim_time:                         0.022
% 3.34/0.98  splitting_time:                         0.
% 3.34/0.98  sem_filter_time:                        0.
% 3.34/0.98  monotx_time:                            0.
% 3.34/0.98  subtype_inf_time:                       0.
% 3.34/0.98  
% 3.34/0.98  ------ Problem properties
% 3.34/0.98  
% 3.34/0.98  clauses:                                35
% 3.34/0.98  conjectures:                            10
% 3.34/0.98  epr:                                    13
% 3.34/0.98  horn:                                   26
% 3.34/0.98  ground:                                 10
% 3.34/0.98  unary:                                  14
% 3.34/0.98  binary:                                 8
% 3.34/0.98  lits:                                   92
% 3.34/0.98  lits_eq:                                15
% 3.34/0.98  fd_pure:                                0
% 3.34/0.98  fd_pseudo:                              0
% 3.34/0.98  fd_cond:                                6
% 3.34/0.98  fd_pseudo_cond:                         0
% 3.34/0.98  ac_symbols:                             0
% 3.34/0.98  
% 3.34/0.98  ------ Propositional Solver
% 3.34/0.98  
% 3.34/0.98  prop_solver_calls:                      29
% 3.34/0.98  prop_fast_solver_calls:                 1591
% 3.34/0.98  smt_solver_calls:                       0
% 3.34/0.98  smt_fast_solver_calls:                  0
% 3.34/0.98  prop_num_of_clauses:                    3177
% 3.34/0.98  prop_preprocess_simplified:             9809
% 3.34/0.98  prop_fo_subsumed:                       41
% 3.34/0.98  prop_solver_time:                       0.
% 3.34/0.98  smt_solver_time:                        0.
% 3.34/0.98  smt_fast_solver_time:                   0.
% 3.34/0.98  prop_fast_solver_time:                  0.
% 3.34/0.98  prop_unsat_core_time:                   0.
% 3.34/0.98  
% 3.34/0.98  ------ QBF
% 3.34/0.98  
% 3.34/0.98  qbf_q_res:                              0
% 3.34/0.98  qbf_num_tautologies:                    0
% 3.34/0.98  qbf_prep_cycles:                        0
% 3.34/0.98  
% 3.34/0.98  ------ BMC1
% 3.34/0.98  
% 3.34/0.98  bmc1_current_bound:                     -1
% 3.34/0.98  bmc1_last_solved_bound:                 -1
% 3.34/0.98  bmc1_unsat_core_size:                   -1
% 3.34/0.98  bmc1_unsat_core_parents_size:           -1
% 3.34/0.98  bmc1_merge_next_fun:                    0
% 3.34/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.34/0.98  
% 3.34/0.98  ------ Instantiation
% 3.34/0.98  
% 3.34/0.98  inst_num_of_clauses:                    1014
% 3.34/0.98  inst_num_in_passive:                    416
% 3.34/0.98  inst_num_in_active:                     503
% 3.34/0.98  inst_num_in_unprocessed:                95
% 3.34/0.98  inst_num_of_loops:                      550
% 3.34/0.98  inst_num_of_learning_restarts:          0
% 3.34/0.98  inst_num_moves_active_passive:          44
% 3.34/0.98  inst_lit_activity:                      0
% 3.34/0.98  inst_lit_activity_moves:                0
% 3.34/0.98  inst_num_tautologies:                   0
% 3.34/0.98  inst_num_prop_implied:                  0
% 3.34/0.98  inst_num_existing_simplified:           0
% 3.34/0.98  inst_num_eq_res_simplified:             0
% 3.34/0.98  inst_num_child_elim:                    0
% 3.34/0.98  inst_num_of_dismatching_blockings:      225
% 3.34/0.98  inst_num_of_non_proper_insts:           862
% 3.34/0.98  inst_num_of_duplicates:                 0
% 3.34/0.98  inst_inst_num_from_inst_to_res:         0
% 3.34/0.98  inst_dismatching_checking_time:         0.
% 3.34/0.98  
% 3.34/0.98  ------ Resolution
% 3.34/0.98  
% 3.34/0.98  res_num_of_clauses:                     0
% 3.34/0.98  res_num_in_passive:                     0
% 3.34/0.98  res_num_in_active:                      0
% 3.34/0.98  res_num_of_loops:                       177
% 3.34/0.98  res_forward_subset_subsumed:            46
% 3.34/0.98  res_backward_subset_subsumed:           0
% 3.34/0.98  res_forward_subsumed:                   0
% 3.34/0.98  res_backward_subsumed:                  0
% 3.34/0.98  res_forward_subsumption_resolution:     0
% 3.34/0.98  res_backward_subsumption_resolution:    0
% 3.34/0.98  res_clause_to_clause_subsumption:       433
% 3.34/0.98  res_orphan_elimination:                 0
% 3.34/0.98  res_tautology_del:                      49
% 3.34/0.98  res_num_eq_res_simplified:              0
% 3.34/0.98  res_num_sel_changes:                    0
% 3.34/0.98  res_moves_from_active_to_pass:          0
% 3.34/0.98  
% 3.34/0.98  ------ Superposition
% 3.34/0.98  
% 3.34/0.98  sup_time_total:                         0.
% 3.34/0.98  sup_time_generating:                    0.
% 3.34/0.98  sup_time_sim_full:                      0.
% 3.34/0.98  sup_time_sim_immed:                     0.
% 3.34/0.98  
% 3.34/0.98  sup_num_of_clauses:                     135
% 3.34/0.98  sup_num_in_active:                      84
% 3.34/0.98  sup_num_in_passive:                     51
% 3.34/0.98  sup_num_of_loops:                       109
% 3.34/0.98  sup_fw_superposition:                   92
% 3.34/0.98  sup_bw_superposition:                   53
% 3.34/0.98  sup_immediate_simplified:               22
% 3.34/0.98  sup_given_eliminated:                   1
% 3.34/0.98  comparisons_done:                       0
% 3.34/0.98  comparisons_avoided:                    7
% 3.34/0.98  
% 3.34/0.98  ------ Simplifications
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  sim_fw_subset_subsumed:                 8
% 3.34/0.98  sim_bw_subset_subsumed:                 5
% 3.34/0.98  sim_fw_subsumed:                        8
% 3.34/0.98  sim_bw_subsumed:                        2
% 3.34/0.98  sim_fw_subsumption_res:                 0
% 3.34/0.98  sim_bw_subsumption_res:                 0
% 3.34/0.98  sim_tautology_del:                      4
% 3.34/0.98  sim_eq_tautology_del:                   6
% 3.34/0.98  sim_eq_res_simp:                        0
% 3.34/0.98  sim_fw_demodulated:                     7
% 3.34/0.98  sim_bw_demodulated:                     23
% 3.34/0.98  sim_light_normalised:                   1
% 3.34/0.98  sim_joinable_taut:                      0
% 3.34/0.98  sim_joinable_simp:                      0
% 3.34/0.98  sim_ac_normalised:                      0
% 3.34/0.98  sim_smt_subsumption:                    0
% 3.34/0.98  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:47 EST 2020

% Result     : Theorem 7.72s
% Output     : CNFRefutation 7.72s
% Verified   : 
% Statistics : Number of formulae       :  212 (1444 expanded)
%              Number of clauses        :  131 ( 439 expanded)
%              Number of leaves         :   26 ( 478 expanded)
%              Depth                    :   22
%              Number of atoms          :  760 (10158 expanded)
%              Number of equality atoms :  354 (2905 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k7_partfun1(X0,X4,k1_funct_1(X3,sK9)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK9)
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK9,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
            ( k7_partfun1(X0,sK8,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK8),X5)
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK8))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
                ( k7_partfun1(X0,X4,k1_funct_1(sK7,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK7,X4),X5)
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK7),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK7,X1,X2)
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
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
                  ( k7_partfun1(sK4,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK5,sK6,sK4,X3,X4),X5)
                  & k1_xboole_0 != sK5
                  & r1_tarski(k2_relset_1(sK5,sK6,X3),k1_relset_1(sK6,sK4,X4))
                  & m1_subset_1(X5,sK5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
          & v1_funct_2(X3,sK5,sK6)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9)
    & k1_xboole_0 != sK5
    & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    & m1_subset_1(sK9,sK5)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7)
    & ~ v1_xboole_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f36,f51,f50,f49,f48])).

fof(f84,plain,(
    m1_subset_1(sK9,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,(
    r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f25])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f78,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f41])).

fof(f45,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f42,f45,f44,f43])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f58,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f89,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK9,sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2044,plain,
    ( m1_subset_1(sK9,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2060,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3586,plain,
    ( r2_hidden(sK9,sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2044,c_2060])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2041,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2052,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2950,plain,
    ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2041,c_2052])).

cnf(c_21,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_485,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK5,sK6,sK7) != k2_relat_1(X0)
    | k1_relset_1(sK6,sK4,sK8) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_486,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relset_1(sK6,sK4,sK8))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK5,sK6,sK7) != k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_2034,plain,
    ( k2_relset_1(sK5,sK6,sK7) != k2_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relset_1(sK6,sK4,sK8)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_3216,plain,
    ( k2_relat_1(X0) != k2_relat_1(sK7)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relset_1(sK6,sK4,sK8)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2950,c_2034])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2043,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2053,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2952,plain,
    ( k1_relset_1(sK6,sK4,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_2043,c_2053])).

cnf(c_3217,plain,
    ( k2_relat_1(X0) != k2_relat_1(sK7)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relat_1(sK8)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3216,c_2952])).

cnf(c_4434,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k1_relat_1(sK8)))) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3217])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_36,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_38,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2178,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2383,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2178])).

cnf(c_2384,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2383])).

cnf(c_6396,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k1_relat_1(sK8)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4434,c_36,c_38,c_2384])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2046,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4078,plain,
    ( k1_relset_1(sK5,sK6,sK7) = sK5
    | sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2041,c_2046])).

cnf(c_2953,plain,
    ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2041,c_2053])).

cnf(c_4079,plain,
    ( k1_relat_1(sK7) = sK5
    | sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4078,c_2953])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_37,plain,
    ( v1_funct_2(sK7,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1532,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2137,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_1532])).

cnf(c_2144,plain,
    ( v1_xboole_0(sK6)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2137])).

cnf(c_4498,plain,
    ( k1_relat_1(sK7) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4079,c_34,c_37,c_2,c_2144])).

cnf(c_6400,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK8)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6396,c_4498])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2045,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6405,plain,
    ( k1_relat_1(sK8) = k1_xboole_0
    | v1_funct_2(sK7,sK5,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k1_relat_1(sK8)) = iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_6400,c_2045])).

cnf(c_22,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_467,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK5,sK6,sK7) != k2_relat_1(X0)
    | k1_relset_1(sK6,sK4,sK8) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_468,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k1_relset_1(sK6,sK4,sK8))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK5,sK6,sK7) != k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_2035,plain,
    ( k2_relset_1(sK5,sK6,sK7) != k2_relat_1(X0)
    | v1_funct_2(X0,k1_relat_1(X0),k1_relset_1(sK6,sK4,sK8)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_3215,plain,
    ( k2_relat_1(X0) != k2_relat_1(sK7)
    | v1_funct_2(X0,k1_relat_1(X0),k1_relset_1(sK6,sK4,sK8)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2950,c_2035])).

cnf(c_3218,plain,
    ( k2_relat_1(X0) != k2_relat_1(sK7)
    | v1_funct_2(X0,k1_relat_1(X0),k1_relat_1(sK8)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3215,c_2952])).

cnf(c_4366,plain,
    ( v1_funct_2(sK7,k1_relat_1(sK7),k1_relat_1(sK8)) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3218])).

cnf(c_6328,plain,
    ( v1_funct_2(sK7,k1_relat_1(sK7),k1_relat_1(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4366,c_36,c_38,c_2384])).

cnf(c_6332,plain,
    ( v1_funct_2(sK7,sK5,k1_relat_1(sK8)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6328,c_4498])).

cnf(c_21905,plain,
    ( r2_hidden(k1_funct_1(sK7,X0),k1_relat_1(sK8)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | k1_relat_1(sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6405,c_36,c_6332])).

cnf(c_21906,plain,
    ( k1_relat_1(sK8) = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k1_relat_1(sK8)) = iProver_top ),
    inference(renaming,[status(thm)],[c_21905])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_19,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_9,c_19])).

cnf(c_365,plain,
    ( ~ v1_funct_1(X0)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_361,c_8])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(renaming,[status(thm)],[c_365])).

cnf(c_2037,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_2900,plain,
    ( k7_partfun1(sK4,sK8,X0) = k1_funct_1(sK8,X0)
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2043,c_2037])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_39,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3321,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | k7_partfun1(sK4,sK8,X0) = k1_funct_1(sK8,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2900,c_39])).

cnf(c_3322,plain,
    ( k7_partfun1(sK4,sK8,X0) = k1_funct_1(sK8,X0)
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3321])).

cnf(c_21913,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,X0)) = k1_funct_1(sK8,k1_funct_1(sK7,X0))
    | k1_relat_1(sK8) = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_21906,c_3322])).

cnf(c_22118,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | k1_relat_1(sK8) = k1_xboole_0
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3586,c_21913])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_25,negated_conjecture,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_105,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1530,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1559,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1530])).

cnf(c_1531,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2127,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_1531])).

cnf(c_2128,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2127])).

cnf(c_2104,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != X0
    | k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9)
    | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != X0 ),
    inference(instantiation,[status(thm)],[c_1531])).

cnf(c_2187,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9)
    | k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_2104])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k1_funct_1(X4,k1_funct_1(X0,X5))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_431,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X2)
    | k2_relset_1(X1,X2,X0) != k2_relset_1(sK5,sK6,sK7)
    | k1_relset_1(X2,X5,X4) != k1_relset_1(sK6,sK4,sK8)
    | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_2036,plain,
    ( k2_relset_1(X0,X1,X2) != k2_relset_1(sK5,sK6,sK7)
    | k1_relset_1(X1,X3,X4) != k1_relset_1(sK6,sK4,sK8)
    | k1_funct_1(k8_funct_2(X0,X1,X3,X2,X4),X5) = k1_funct_1(X4,k1_funct_1(X2,X5))
    | k1_xboole_0 = X0
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_2690,plain,
    ( k1_relset_1(sK6,X0,X1) != k1_relset_1(sK6,sK4,sK8)
    | k1_funct_1(k8_funct_2(sK5,sK6,X0,sK7,X1),X2) = k1_funct_1(X1,k1_funct_1(sK7,X2))
    | sK5 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) != iProver_top
    | m1_subset_1(X2,sK5) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2036])).

cnf(c_35,plain,
    ( v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2695,plain,
    ( m1_subset_1(X2,sK5) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) != iProver_top
    | k1_funct_1(k8_funct_2(sK5,sK6,X0,sK7,X1),X2) = k1_funct_1(X1,k1_funct_1(sK7,X2))
    | k1_relset_1(sK6,X0,X1) != k1_relset_1(sK6,sK4,sK8)
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2690,c_35,c_36,c_37,c_38,c_26,c_1559,c_2128])).

cnf(c_2696,plain,
    ( k1_relset_1(sK6,X0,X1) != k1_relset_1(sK6,sK4,sK8)
    | k1_funct_1(k8_funct_2(sK5,sK6,X0,sK7,X1),X2) = k1_funct_1(X1,k1_funct_1(sK7,X2))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) != iProver_top
    | m1_subset_1(X2,sK5) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2695])).

cnf(c_2701,plain,
    ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),X0) = k1_funct_1(sK8,k1_funct_1(sK7,X0))
    | m1_subset_1(X0,sK5) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2696])).

cnf(c_40,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2808,plain,
    ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),X0) = k1_funct_1(sK8,k1_funct_1(sK7,X0))
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2701,c_39,c_40])).

cnf(c_2814,plain,
    ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) = k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
    inference(superposition,[status(thm)],[c_2044,c_2808])).

cnf(c_5,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2058,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2057,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4192,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2058,c_2057])).

cnf(c_9460,plain,
    ( k1_relat_1(sK7) = X0
    | r2_hidden(sK1(sK7,X0),X0) = iProver_top
    | r2_hidden(sK1(sK7,X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4498,c_4192])).

cnf(c_9491,plain,
    ( sK5 = X0
    | r2_hidden(sK1(sK7,X0),X0) = iProver_top
    | r2_hidden(sK1(sK7,X0),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9460,c_4498])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2062,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9661,plain,
    ( sK5 = X0
    | r2_hidden(sK1(sK7,X0),X0) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9491,c_2062])).

cnf(c_10176,plain,
    ( sK5 = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9661,c_2062])).

cnf(c_10192,plain,
    ( sK5 = k1_xboole_0
    | v1_xboole_0(sK5) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10176])).

cnf(c_22208,plain,
    ( k1_relat_1(sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22118,c_26,c_25,c_105,c_1559,c_2128,c_2187,c_2814,c_10192])).

cnf(c_21911,plain,
    ( k1_relat_1(sK8) = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21906,c_2062])).

cnf(c_2842,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1530])).

cnf(c_3958,plain,
    ( X0 != X1
    | X0 = k1_relat_1(X2)
    | k1_relat_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1531])).

cnf(c_3959,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3958])).

cnf(c_2189,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_1531])).

cnf(c_2424,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2189])).

cnf(c_4183,plain,
    ( k1_relat_1(X0) != sK5
    | sK5 = k1_relat_1(X0)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2424])).

cnf(c_4184,plain,
    ( k1_relat_1(k1_xboole_0) != sK5
    | sK5 = k1_relat_1(k1_xboole_0)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_4183])).

cnf(c_4191,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2058,c_2062])).

cnf(c_5746,plain,
    ( k1_relat_1(X0) = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4191,c_2062])).

cnf(c_5757,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5746])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2056,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2991,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2056,c_2062])).

cnf(c_4645,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4498,c_2991])).

cnf(c_5748,plain,
    ( k1_relat_1(X0) = sK5
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4191,c_4645])).

cnf(c_5763,plain,
    ( k1_relat_1(k1_xboole_0) = sK5
    | v1_xboole_0(sK7) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5748])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2054,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6403,plain,
    ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_6400,c_2054])).

cnf(c_7761,plain,
    ( X0 != k1_relat_1(X1)
    | sK5 = X0
    | sK5 != k1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_2189])).

cnf(c_7762,plain,
    ( sK5 != k1_relat_1(k1_xboole_0)
    | sK5 = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7761])).

cnf(c_21952,plain,
    ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21911,c_26,c_105,c_1559,c_2128,c_2842,c_3959,c_4184,c_5757,c_5763,c_6403,c_7762])).

cnf(c_22211,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22208,c_21952])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22211,c_105])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.72/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.72/1.49  
% 7.72/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.72/1.49  
% 7.72/1.49  ------  iProver source info
% 7.72/1.49  
% 7.72/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.72/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.72/1.49  git: non_committed_changes: false
% 7.72/1.49  git: last_make_outside_of_git: false
% 7.72/1.49  
% 7.72/1.49  ------ 
% 7.72/1.49  
% 7.72/1.49  ------ Input Options
% 7.72/1.49  
% 7.72/1.49  --out_options                           all
% 7.72/1.49  --tptp_safe_out                         true
% 7.72/1.49  --problem_path                          ""
% 7.72/1.49  --include_path                          ""
% 7.72/1.49  --clausifier                            res/vclausify_rel
% 7.72/1.49  --clausifier_options                    ""
% 7.72/1.49  --stdin                                 false
% 7.72/1.49  --stats_out                             all
% 7.72/1.49  
% 7.72/1.49  ------ General Options
% 7.72/1.49  
% 7.72/1.49  --fof                                   false
% 7.72/1.49  --time_out_real                         305.
% 7.72/1.49  --time_out_virtual                      -1.
% 7.72/1.49  --symbol_type_check                     false
% 7.72/1.49  --clausify_out                          false
% 7.72/1.49  --sig_cnt_out                           false
% 7.72/1.49  --trig_cnt_out                          false
% 7.72/1.49  --trig_cnt_out_tolerance                1.
% 7.72/1.49  --trig_cnt_out_sk_spl                   false
% 7.72/1.49  --abstr_cl_out                          false
% 7.72/1.49  
% 7.72/1.49  ------ Global Options
% 7.72/1.49  
% 7.72/1.49  --schedule                              default
% 7.72/1.49  --add_important_lit                     false
% 7.72/1.49  --prop_solver_per_cl                    1000
% 7.72/1.49  --min_unsat_core                        false
% 7.72/1.49  --soft_assumptions                      false
% 7.72/1.49  --soft_lemma_size                       3
% 7.72/1.49  --prop_impl_unit_size                   0
% 7.72/1.49  --prop_impl_unit                        []
% 7.72/1.49  --share_sel_clauses                     true
% 7.72/1.49  --reset_solvers                         false
% 7.72/1.49  --bc_imp_inh                            [conj_cone]
% 7.72/1.49  --conj_cone_tolerance                   3.
% 7.72/1.49  --extra_neg_conj                        none
% 7.72/1.49  --large_theory_mode                     true
% 7.72/1.49  --prolific_symb_bound                   200
% 7.72/1.49  --lt_threshold                          2000
% 7.72/1.49  --clause_weak_htbl                      true
% 7.72/1.49  --gc_record_bc_elim                     false
% 7.72/1.49  
% 7.72/1.49  ------ Preprocessing Options
% 7.72/1.49  
% 7.72/1.49  --preprocessing_flag                    true
% 7.72/1.49  --time_out_prep_mult                    0.1
% 7.72/1.49  --splitting_mode                        input
% 7.72/1.49  --splitting_grd                         true
% 7.72/1.49  --splitting_cvd                         false
% 7.72/1.49  --splitting_cvd_svl                     false
% 7.72/1.49  --splitting_nvd                         32
% 7.72/1.49  --sub_typing                            true
% 7.72/1.49  --prep_gs_sim                           true
% 7.72/1.49  --prep_unflatten                        true
% 7.72/1.49  --prep_res_sim                          true
% 7.72/1.49  --prep_upred                            true
% 7.72/1.49  --prep_sem_filter                       exhaustive
% 7.72/1.49  --prep_sem_filter_out                   false
% 7.72/1.49  --pred_elim                             true
% 7.72/1.49  --res_sim_input                         true
% 7.72/1.49  --eq_ax_congr_red                       true
% 7.72/1.49  --pure_diseq_elim                       true
% 7.72/1.49  --brand_transform                       false
% 7.72/1.49  --non_eq_to_eq                          false
% 7.72/1.49  --prep_def_merge                        true
% 7.72/1.49  --prep_def_merge_prop_impl              false
% 7.72/1.49  --prep_def_merge_mbd                    true
% 7.72/1.49  --prep_def_merge_tr_red                 false
% 7.72/1.49  --prep_def_merge_tr_cl                  false
% 7.72/1.49  --smt_preprocessing                     true
% 7.72/1.49  --smt_ac_axioms                         fast
% 7.72/1.49  --preprocessed_out                      false
% 7.72/1.49  --preprocessed_stats                    false
% 7.72/1.49  
% 7.72/1.49  ------ Abstraction refinement Options
% 7.72/1.49  
% 7.72/1.49  --abstr_ref                             []
% 7.72/1.49  --abstr_ref_prep                        false
% 7.72/1.49  --abstr_ref_until_sat                   false
% 7.72/1.49  --abstr_ref_sig_restrict                funpre
% 7.72/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.72/1.49  --abstr_ref_under                       []
% 7.72/1.49  
% 7.72/1.49  ------ SAT Options
% 7.72/1.49  
% 7.72/1.49  --sat_mode                              false
% 7.72/1.49  --sat_fm_restart_options                ""
% 7.72/1.49  --sat_gr_def                            false
% 7.72/1.49  --sat_epr_types                         true
% 7.72/1.49  --sat_non_cyclic_types                  false
% 7.72/1.49  --sat_finite_models                     false
% 7.72/1.49  --sat_fm_lemmas                         false
% 7.72/1.49  --sat_fm_prep                           false
% 7.72/1.49  --sat_fm_uc_incr                        true
% 7.72/1.49  --sat_out_model                         small
% 7.72/1.49  --sat_out_clauses                       false
% 7.72/1.49  
% 7.72/1.49  ------ QBF Options
% 7.72/1.49  
% 7.72/1.49  --qbf_mode                              false
% 7.72/1.49  --qbf_elim_univ                         false
% 7.72/1.49  --qbf_dom_inst                          none
% 7.72/1.49  --qbf_dom_pre_inst                      false
% 7.72/1.49  --qbf_sk_in                             false
% 7.72/1.49  --qbf_pred_elim                         true
% 7.72/1.49  --qbf_split                             512
% 7.72/1.49  
% 7.72/1.49  ------ BMC1 Options
% 7.72/1.49  
% 7.72/1.49  --bmc1_incremental                      false
% 7.72/1.49  --bmc1_axioms                           reachable_all
% 7.72/1.49  --bmc1_min_bound                        0
% 7.72/1.49  --bmc1_max_bound                        -1
% 7.72/1.49  --bmc1_max_bound_default                -1
% 7.72/1.49  --bmc1_symbol_reachability              true
% 7.72/1.49  --bmc1_property_lemmas                  false
% 7.72/1.49  --bmc1_k_induction                      false
% 7.72/1.49  --bmc1_non_equiv_states                 false
% 7.72/1.49  --bmc1_deadlock                         false
% 7.72/1.49  --bmc1_ucm                              false
% 7.72/1.49  --bmc1_add_unsat_core                   none
% 7.72/1.49  --bmc1_unsat_core_children              false
% 7.72/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.72/1.49  --bmc1_out_stat                         full
% 7.72/1.49  --bmc1_ground_init                      false
% 7.72/1.49  --bmc1_pre_inst_next_state              false
% 7.72/1.49  --bmc1_pre_inst_state                   false
% 7.72/1.49  --bmc1_pre_inst_reach_state             false
% 7.72/1.49  --bmc1_out_unsat_core                   false
% 7.72/1.49  --bmc1_aig_witness_out                  false
% 7.72/1.49  --bmc1_verbose                          false
% 7.72/1.49  --bmc1_dump_clauses_tptp                false
% 7.72/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.72/1.49  --bmc1_dump_file                        -
% 7.72/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.72/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.72/1.49  --bmc1_ucm_extend_mode                  1
% 7.72/1.49  --bmc1_ucm_init_mode                    2
% 7.72/1.49  --bmc1_ucm_cone_mode                    none
% 7.72/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.72/1.49  --bmc1_ucm_relax_model                  4
% 7.72/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.72/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.72/1.49  --bmc1_ucm_layered_model                none
% 7.72/1.50  --bmc1_ucm_max_lemma_size               10
% 7.72/1.50  
% 7.72/1.50  ------ AIG Options
% 7.72/1.50  
% 7.72/1.50  --aig_mode                              false
% 7.72/1.50  
% 7.72/1.50  ------ Instantiation Options
% 7.72/1.50  
% 7.72/1.50  --instantiation_flag                    true
% 7.72/1.50  --inst_sos_flag                         true
% 7.72/1.50  --inst_sos_phase                        true
% 7.72/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.72/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.72/1.50  --inst_lit_sel_side                     num_symb
% 7.72/1.50  --inst_solver_per_active                1400
% 7.72/1.50  --inst_solver_calls_frac                1.
% 7.72/1.50  --inst_passive_queue_type               priority_queues
% 7.72/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.72/1.50  --inst_passive_queues_freq              [25;2]
% 7.72/1.50  --inst_dismatching                      true
% 7.72/1.50  --inst_eager_unprocessed_to_passive     true
% 7.72/1.50  --inst_prop_sim_given                   true
% 7.72/1.50  --inst_prop_sim_new                     false
% 7.72/1.50  --inst_subs_new                         false
% 7.72/1.50  --inst_eq_res_simp                      false
% 7.72/1.50  --inst_subs_given                       false
% 7.72/1.50  --inst_orphan_elimination               true
% 7.72/1.50  --inst_learning_loop_flag               true
% 7.72/1.50  --inst_learning_start                   3000
% 7.72/1.50  --inst_learning_factor                  2
% 7.72/1.50  --inst_start_prop_sim_after_learn       3
% 7.72/1.50  --inst_sel_renew                        solver
% 7.72/1.50  --inst_lit_activity_flag                true
% 7.72/1.50  --inst_restr_to_given                   false
% 7.72/1.50  --inst_activity_threshold               500
% 7.72/1.50  --inst_out_proof                        true
% 7.72/1.50  
% 7.72/1.50  ------ Resolution Options
% 7.72/1.50  
% 7.72/1.50  --resolution_flag                       true
% 7.72/1.50  --res_lit_sel                           adaptive
% 7.72/1.50  --res_lit_sel_side                      none
% 7.72/1.50  --res_ordering                          kbo
% 7.72/1.50  --res_to_prop_solver                    active
% 7.72/1.50  --res_prop_simpl_new                    false
% 7.72/1.50  --res_prop_simpl_given                  true
% 7.72/1.50  --res_passive_queue_type                priority_queues
% 7.72/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.72/1.50  --res_passive_queues_freq               [15;5]
% 7.72/1.50  --res_forward_subs                      full
% 7.72/1.50  --res_backward_subs                     full
% 7.72/1.50  --res_forward_subs_resolution           true
% 7.72/1.50  --res_backward_subs_resolution          true
% 7.72/1.50  --res_orphan_elimination                true
% 7.72/1.50  --res_time_limit                        2.
% 7.72/1.50  --res_out_proof                         true
% 7.72/1.50  
% 7.72/1.50  ------ Superposition Options
% 7.72/1.50  
% 7.72/1.50  --superposition_flag                    true
% 7.72/1.50  --sup_passive_queue_type                priority_queues
% 7.72/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.72/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.72/1.50  --demod_completeness_check              fast
% 7.72/1.50  --demod_use_ground                      true
% 7.72/1.50  --sup_to_prop_solver                    passive
% 7.72/1.50  --sup_prop_simpl_new                    true
% 7.72/1.50  --sup_prop_simpl_given                  true
% 7.72/1.50  --sup_fun_splitting                     true
% 7.72/1.50  --sup_smt_interval                      50000
% 7.72/1.50  
% 7.72/1.50  ------ Superposition Simplification Setup
% 7.72/1.50  
% 7.72/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.72/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.72/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.72/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.72/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.72/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.72/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.72/1.50  --sup_immed_triv                        [TrivRules]
% 7.72/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.72/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.72/1.50  --sup_immed_bw_main                     []
% 7.72/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.72/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.72/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.72/1.50  --sup_input_bw                          []
% 7.72/1.50  
% 7.72/1.50  ------ Combination Options
% 7.72/1.50  
% 7.72/1.50  --comb_res_mult                         3
% 7.72/1.50  --comb_sup_mult                         2
% 7.72/1.50  --comb_inst_mult                        10
% 7.72/1.50  
% 7.72/1.50  ------ Debug Options
% 7.72/1.50  
% 7.72/1.50  --dbg_backtrace                         false
% 7.72/1.50  --dbg_dump_prop_clauses                 false
% 7.72/1.50  --dbg_dump_prop_clauses_file            -
% 7.72/1.50  --dbg_out_stat                          false
% 7.72/1.50  ------ Parsing...
% 7.72/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.72/1.50  
% 7.72/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.72/1.50  
% 7.72/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.72/1.50  
% 7.72/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.72/1.50  ------ Proving...
% 7.72/1.50  ------ Problem Properties 
% 7.72/1.50  
% 7.72/1.50  
% 7.72/1.50  clauses                                 32
% 7.72/1.50  conjectures                             9
% 7.72/1.50  EPR                                     9
% 7.72/1.50  Horn                                    23
% 7.72/1.50  unary                                   10
% 7.72/1.50  binary                                  7
% 7.72/1.50  lits                                    86
% 7.72/1.50  lits eq                                 23
% 7.72/1.50  fd_pure                                 0
% 7.72/1.50  fd_pseudo                               0
% 7.72/1.50  fd_cond                                 5
% 7.72/1.50  fd_pseudo_cond                          2
% 7.72/1.50  AC symbols                              0
% 7.72/1.50  
% 7.72/1.50  ------ Schedule dynamic 5 is on 
% 7.72/1.50  
% 7.72/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.72/1.50  
% 7.72/1.50  
% 7.72/1.50  ------ 
% 7.72/1.50  Current options:
% 7.72/1.50  ------ 
% 7.72/1.50  
% 7.72/1.50  ------ Input Options
% 7.72/1.50  
% 7.72/1.50  --out_options                           all
% 7.72/1.50  --tptp_safe_out                         true
% 7.72/1.50  --problem_path                          ""
% 7.72/1.50  --include_path                          ""
% 7.72/1.50  --clausifier                            res/vclausify_rel
% 7.72/1.50  --clausifier_options                    ""
% 7.72/1.50  --stdin                                 false
% 7.72/1.50  --stats_out                             all
% 7.72/1.50  
% 7.72/1.50  ------ General Options
% 7.72/1.50  
% 7.72/1.50  --fof                                   false
% 7.72/1.50  --time_out_real                         305.
% 7.72/1.50  --time_out_virtual                      -1.
% 7.72/1.50  --symbol_type_check                     false
% 7.72/1.50  --clausify_out                          false
% 7.72/1.50  --sig_cnt_out                           false
% 7.72/1.50  --trig_cnt_out                          false
% 7.72/1.50  --trig_cnt_out_tolerance                1.
% 7.72/1.50  --trig_cnt_out_sk_spl                   false
% 7.72/1.50  --abstr_cl_out                          false
% 7.72/1.50  
% 7.72/1.50  ------ Global Options
% 7.72/1.50  
% 7.72/1.50  --schedule                              default
% 7.72/1.50  --add_important_lit                     false
% 7.72/1.50  --prop_solver_per_cl                    1000
% 7.72/1.50  --min_unsat_core                        false
% 7.72/1.50  --soft_assumptions                      false
% 7.72/1.50  --soft_lemma_size                       3
% 7.72/1.50  --prop_impl_unit_size                   0
% 7.72/1.50  --prop_impl_unit                        []
% 7.72/1.50  --share_sel_clauses                     true
% 7.72/1.50  --reset_solvers                         false
% 7.72/1.50  --bc_imp_inh                            [conj_cone]
% 7.72/1.50  --conj_cone_tolerance                   3.
% 7.72/1.50  --extra_neg_conj                        none
% 7.72/1.50  --large_theory_mode                     true
% 7.72/1.50  --prolific_symb_bound                   200
% 7.72/1.50  --lt_threshold                          2000
% 7.72/1.50  --clause_weak_htbl                      true
% 7.72/1.50  --gc_record_bc_elim                     false
% 7.72/1.50  
% 7.72/1.50  ------ Preprocessing Options
% 7.72/1.50  
% 7.72/1.50  --preprocessing_flag                    true
% 7.72/1.50  --time_out_prep_mult                    0.1
% 7.72/1.50  --splitting_mode                        input
% 7.72/1.50  --splitting_grd                         true
% 7.72/1.50  --splitting_cvd                         false
% 7.72/1.50  --splitting_cvd_svl                     false
% 7.72/1.50  --splitting_nvd                         32
% 7.72/1.50  --sub_typing                            true
% 7.72/1.50  --prep_gs_sim                           true
% 7.72/1.50  --prep_unflatten                        true
% 7.72/1.50  --prep_res_sim                          true
% 7.72/1.50  --prep_upred                            true
% 7.72/1.50  --prep_sem_filter                       exhaustive
% 7.72/1.50  --prep_sem_filter_out                   false
% 7.72/1.50  --pred_elim                             true
% 7.72/1.50  --res_sim_input                         true
% 7.72/1.50  --eq_ax_congr_red                       true
% 7.72/1.50  --pure_diseq_elim                       true
% 7.72/1.50  --brand_transform                       false
% 7.72/1.50  --non_eq_to_eq                          false
% 7.72/1.50  --prep_def_merge                        true
% 7.72/1.50  --prep_def_merge_prop_impl              false
% 7.72/1.50  --prep_def_merge_mbd                    true
% 7.72/1.50  --prep_def_merge_tr_red                 false
% 7.72/1.50  --prep_def_merge_tr_cl                  false
% 7.72/1.50  --smt_preprocessing                     true
% 7.72/1.50  --smt_ac_axioms                         fast
% 7.72/1.50  --preprocessed_out                      false
% 7.72/1.50  --preprocessed_stats                    false
% 7.72/1.50  
% 7.72/1.50  ------ Abstraction refinement Options
% 7.72/1.50  
% 7.72/1.50  --abstr_ref                             []
% 7.72/1.50  --abstr_ref_prep                        false
% 7.72/1.50  --abstr_ref_until_sat                   false
% 7.72/1.50  --abstr_ref_sig_restrict                funpre
% 7.72/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.72/1.50  --abstr_ref_under                       []
% 7.72/1.50  
% 7.72/1.50  ------ SAT Options
% 7.72/1.50  
% 7.72/1.50  --sat_mode                              false
% 7.72/1.50  --sat_fm_restart_options                ""
% 7.72/1.50  --sat_gr_def                            false
% 7.72/1.50  --sat_epr_types                         true
% 7.72/1.50  --sat_non_cyclic_types                  false
% 7.72/1.50  --sat_finite_models                     false
% 7.72/1.50  --sat_fm_lemmas                         false
% 7.72/1.50  --sat_fm_prep                           false
% 7.72/1.50  --sat_fm_uc_incr                        true
% 7.72/1.50  --sat_out_model                         small
% 7.72/1.50  --sat_out_clauses                       false
% 7.72/1.50  
% 7.72/1.50  ------ QBF Options
% 7.72/1.50  
% 7.72/1.50  --qbf_mode                              false
% 7.72/1.50  --qbf_elim_univ                         false
% 7.72/1.50  --qbf_dom_inst                          none
% 7.72/1.50  --qbf_dom_pre_inst                      false
% 7.72/1.50  --qbf_sk_in                             false
% 7.72/1.50  --qbf_pred_elim                         true
% 7.72/1.50  --qbf_split                             512
% 7.72/1.50  
% 7.72/1.50  ------ BMC1 Options
% 7.72/1.50  
% 7.72/1.50  --bmc1_incremental                      false
% 7.72/1.50  --bmc1_axioms                           reachable_all
% 7.72/1.50  --bmc1_min_bound                        0
% 7.72/1.50  --bmc1_max_bound                        -1
% 7.72/1.50  --bmc1_max_bound_default                -1
% 7.72/1.50  --bmc1_symbol_reachability              true
% 7.72/1.50  --bmc1_property_lemmas                  false
% 7.72/1.50  --bmc1_k_induction                      false
% 7.72/1.50  --bmc1_non_equiv_states                 false
% 7.72/1.50  --bmc1_deadlock                         false
% 7.72/1.50  --bmc1_ucm                              false
% 7.72/1.50  --bmc1_add_unsat_core                   none
% 7.72/1.50  --bmc1_unsat_core_children              false
% 7.72/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.72/1.50  --bmc1_out_stat                         full
% 7.72/1.50  --bmc1_ground_init                      false
% 7.72/1.50  --bmc1_pre_inst_next_state              false
% 7.72/1.50  --bmc1_pre_inst_state                   false
% 7.72/1.50  --bmc1_pre_inst_reach_state             false
% 7.72/1.50  --bmc1_out_unsat_core                   false
% 7.72/1.50  --bmc1_aig_witness_out                  false
% 7.72/1.50  --bmc1_verbose                          false
% 7.72/1.50  --bmc1_dump_clauses_tptp                false
% 7.72/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.72/1.50  --bmc1_dump_file                        -
% 7.72/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.72/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.72/1.50  --bmc1_ucm_extend_mode                  1
% 7.72/1.50  --bmc1_ucm_init_mode                    2
% 7.72/1.50  --bmc1_ucm_cone_mode                    none
% 7.72/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.72/1.50  --bmc1_ucm_relax_model                  4
% 7.72/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.72/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.72/1.50  --bmc1_ucm_layered_model                none
% 7.72/1.50  --bmc1_ucm_max_lemma_size               10
% 7.72/1.50  
% 7.72/1.50  ------ AIG Options
% 7.72/1.50  
% 7.72/1.50  --aig_mode                              false
% 7.72/1.50  
% 7.72/1.50  ------ Instantiation Options
% 7.72/1.50  
% 7.72/1.50  --instantiation_flag                    true
% 7.72/1.50  --inst_sos_flag                         true
% 7.72/1.50  --inst_sos_phase                        true
% 7.72/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.72/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.72/1.50  --inst_lit_sel_side                     none
% 7.72/1.50  --inst_solver_per_active                1400
% 7.72/1.50  --inst_solver_calls_frac                1.
% 7.72/1.50  --inst_passive_queue_type               priority_queues
% 7.72/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.72/1.50  --inst_passive_queues_freq              [25;2]
% 7.72/1.50  --inst_dismatching                      true
% 7.72/1.50  --inst_eager_unprocessed_to_passive     true
% 7.72/1.50  --inst_prop_sim_given                   true
% 7.72/1.50  --inst_prop_sim_new                     false
% 7.72/1.50  --inst_subs_new                         false
% 7.72/1.50  --inst_eq_res_simp                      false
% 7.72/1.50  --inst_subs_given                       false
% 7.72/1.50  --inst_orphan_elimination               true
% 7.72/1.50  --inst_learning_loop_flag               true
% 7.72/1.50  --inst_learning_start                   3000
% 7.72/1.50  --inst_learning_factor                  2
% 7.72/1.50  --inst_start_prop_sim_after_learn       3
% 7.72/1.50  --inst_sel_renew                        solver
% 7.72/1.50  --inst_lit_activity_flag                true
% 7.72/1.50  --inst_restr_to_given                   false
% 7.72/1.50  --inst_activity_threshold               500
% 7.72/1.50  --inst_out_proof                        true
% 7.72/1.50  
% 7.72/1.50  ------ Resolution Options
% 7.72/1.50  
% 7.72/1.50  --resolution_flag                       false
% 7.72/1.50  --res_lit_sel                           adaptive
% 7.72/1.50  --res_lit_sel_side                      none
% 7.72/1.50  --res_ordering                          kbo
% 7.72/1.50  --res_to_prop_solver                    active
% 7.72/1.50  --res_prop_simpl_new                    false
% 7.72/1.50  --res_prop_simpl_given                  true
% 7.72/1.50  --res_passive_queue_type                priority_queues
% 7.72/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.72/1.50  --res_passive_queues_freq               [15;5]
% 7.72/1.50  --res_forward_subs                      full
% 7.72/1.50  --res_backward_subs                     full
% 7.72/1.50  --res_forward_subs_resolution           true
% 7.72/1.50  --res_backward_subs_resolution          true
% 7.72/1.50  --res_orphan_elimination                true
% 7.72/1.50  --res_time_limit                        2.
% 7.72/1.50  --res_out_proof                         true
% 7.72/1.50  
% 7.72/1.50  ------ Superposition Options
% 7.72/1.50  
% 7.72/1.50  --superposition_flag                    true
% 7.72/1.50  --sup_passive_queue_type                priority_queues
% 7.72/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.72/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.72/1.50  --demod_completeness_check              fast
% 7.72/1.50  --demod_use_ground                      true
% 7.72/1.50  --sup_to_prop_solver                    passive
% 7.72/1.50  --sup_prop_simpl_new                    true
% 7.72/1.50  --sup_prop_simpl_given                  true
% 7.72/1.50  --sup_fun_splitting                     true
% 7.72/1.50  --sup_smt_interval                      50000
% 7.72/1.50  
% 7.72/1.50  ------ Superposition Simplification Setup
% 7.72/1.50  
% 7.72/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.72/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.72/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.72/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.72/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.72/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.72/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.72/1.50  --sup_immed_triv                        [TrivRules]
% 7.72/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.72/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.72/1.50  --sup_immed_bw_main                     []
% 7.72/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.72/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.72/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.72/1.50  --sup_input_bw                          []
% 7.72/1.50  
% 7.72/1.50  ------ Combination Options
% 7.72/1.50  
% 7.72/1.50  --comb_res_mult                         3
% 7.72/1.50  --comb_sup_mult                         2
% 7.72/1.50  --comb_inst_mult                        10
% 7.72/1.50  
% 7.72/1.50  ------ Debug Options
% 7.72/1.50  
% 7.72/1.50  --dbg_backtrace                         false
% 7.72/1.50  --dbg_dump_prop_clauses                 false
% 7.72/1.50  --dbg_dump_prop_clauses_file            -
% 7.72/1.50  --dbg_out_stat                          false
% 7.72/1.50  
% 7.72/1.50  
% 7.72/1.50  
% 7.72/1.50  
% 7.72/1.50  ------ Proving...
% 7.72/1.50  
% 7.72/1.50  
% 7.72/1.50  % SZS status Theorem for theBenchmark.p
% 7.72/1.50  
% 7.72/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.72/1.50  
% 7.72/1.50  fof(f15,conjecture,(
% 7.72/1.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 7.72/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.50  
% 7.72/1.50  fof(f16,negated_conjecture,(
% 7.72/1.50    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 7.72/1.50    inference(negated_conjecture,[],[f15])).
% 7.72/1.50  
% 7.72/1.50  fof(f35,plain,(
% 7.72/1.50    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 7.72/1.50    inference(ennf_transformation,[],[f16])).
% 7.72/1.50  
% 7.72/1.50  fof(f36,plain,(
% 7.72/1.50    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 7.72/1.50    inference(flattening,[],[f35])).
% 7.72/1.50  
% 7.72/1.50  fof(f51,plain,(
% 7.72/1.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k7_partfun1(X0,X4,k1_funct_1(X3,sK9)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK9) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK9,X1))) )),
% 7.72/1.50    introduced(choice_axiom,[])).
% 7.72/1.50  
% 7.72/1.50  fof(f50,plain,(
% 7.72/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k7_partfun1(X0,sK8,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK8),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK8)) & m1_subset_1(X5,X1)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK8))) )),
% 7.72/1.50    introduced(choice_axiom,[])).
% 7.72/1.50  
% 7.72/1.50  fof(f49,plain,(
% 7.72/1.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(sK7,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK7,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK7),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK7,X1,X2) & v1_funct_1(sK7))) )),
% 7.72/1.50    introduced(choice_axiom,[])).
% 7.72/1.50  
% 7.72/1.50  fof(f48,plain,(
% 7.72/1.50    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(sK4,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK5,sK6,sK4,X3,X4),X5) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,X3),k1_relset_1(sK6,sK4,X4)) & m1_subset_1(X5,sK5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) & ~v1_xboole_0(sK6))),
% 7.72/1.50    introduced(choice_axiom,[])).
% 7.72/1.50  
% 7.72/1.50  fof(f52,plain,(
% 7.72/1.50    (((k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) & m1_subset_1(sK9,sK5)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)) & ~v1_xboole_0(sK6)),
% 7.72/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f36,f51,f50,f49,f48])).
% 7.72/1.50  
% 7.72/1.50  fof(f84,plain,(
% 7.72/1.50    m1_subset_1(sK9,sK5)),
% 7.72/1.50    inference(cnf_transformation,[],[f52])).
% 7.72/1.50  
% 7.72/1.50  fof(f3,axiom,(
% 7.72/1.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.72/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.50  
% 7.72/1.50  fof(f18,plain,(
% 7.72/1.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.72/1.50    inference(ennf_transformation,[],[f3])).
% 7.72/1.50  
% 7.72/1.50  fof(f19,plain,(
% 7.72/1.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.72/1.50    inference(flattening,[],[f18])).
% 7.72/1.50  
% 7.72/1.50  fof(f56,plain,(
% 7.72/1.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.72/1.50    inference(cnf_transformation,[],[f19])).
% 7.72/1.50  
% 7.72/1.50  fof(f81,plain,(
% 7.72/1.50    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 7.72/1.50    inference(cnf_transformation,[],[f52])).
% 7.72/1.50  
% 7.72/1.50  fof(f9,axiom,(
% 7.72/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 7.72/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.50  
% 7.72/1.50  fof(f24,plain,(
% 7.72/1.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.72/1.50    inference(ennf_transformation,[],[f9])).
% 7.72/1.50  
% 7.72/1.50  fof(f65,plain,(
% 7.72/1.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.72/1.50    inference(cnf_transformation,[],[f24])).
% 7.72/1.50  
% 7.72/1.50  fof(f13,axiom,(
% 7.72/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 7.72/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.50  
% 7.72/1.50  fof(f31,plain,(
% 7.72/1.50    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.72/1.50    inference(ennf_transformation,[],[f13])).
% 7.72/1.50  
% 7.72/1.50  fof(f32,plain,(
% 7.72/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.72/1.50    inference(flattening,[],[f31])).
% 7.72/1.50  
% 7.72/1.50  fof(f76,plain,(
% 7.72/1.50    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.72/1.50    inference(cnf_transformation,[],[f32])).
% 7.72/1.50  
% 7.72/1.50  fof(f85,plain,(
% 7.72/1.50    r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))),
% 7.72/1.50    inference(cnf_transformation,[],[f52])).
% 7.72/1.50  
% 7.72/1.50  fof(f83,plain,(
% 7.72/1.50    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))),
% 7.72/1.50    inference(cnf_transformation,[],[f52])).
% 7.72/1.50  
% 7.72/1.50  fof(f8,axiom,(
% 7.72/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.72/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.50  
% 7.72/1.50  fof(f23,plain,(
% 7.72/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.72/1.50    inference(ennf_transformation,[],[f8])).
% 7.72/1.50  
% 7.72/1.50  fof(f64,plain,(
% 7.72/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.72/1.50    inference(cnf_transformation,[],[f23])).
% 7.72/1.50  
% 7.72/1.50  fof(f79,plain,(
% 7.72/1.50    v1_funct_1(sK7)),
% 7.72/1.50    inference(cnf_transformation,[],[f52])).
% 7.72/1.50  
% 7.72/1.50  fof(f5,axiom,(
% 7.72/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.72/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.50  
% 7.72/1.50  fof(f20,plain,(
% 7.72/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.72/1.50    inference(ennf_transformation,[],[f5])).
% 7.72/1.50  
% 7.72/1.50  fof(f61,plain,(
% 7.72/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.72/1.50    inference(cnf_transformation,[],[f20])).
% 7.72/1.50  
% 7.72/1.50  fof(f10,axiom,(
% 7.72/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.72/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.50  
% 7.72/1.50  fof(f25,plain,(
% 7.72/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.72/1.50    inference(ennf_transformation,[],[f10])).
% 7.72/1.50  
% 7.72/1.50  fof(f26,plain,(
% 7.72/1.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.72/1.50    inference(flattening,[],[f25])).
% 7.72/1.50  
% 7.72/1.50  fof(f47,plain,(
% 7.72/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.72/1.50    inference(nnf_transformation,[],[f26])).
% 7.72/1.50  
% 7.72/1.50  fof(f66,plain,(
% 7.72/1.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.72/1.50    inference(cnf_transformation,[],[f47])).
% 7.72/1.50  
% 7.72/1.50  fof(f78,plain,(
% 7.72/1.50    ~v1_xboole_0(sK6)),
% 7.72/1.50    inference(cnf_transformation,[],[f52])).
% 7.72/1.50  
% 7.72/1.50  fof(f80,plain,(
% 7.72/1.50    v1_funct_2(sK7,sK5,sK6)),
% 7.72/1.50    inference(cnf_transformation,[],[f52])).
% 7.72/1.50  
% 7.72/1.50  fof(f2,axiom,(
% 7.72/1.50    v1_xboole_0(k1_xboole_0)),
% 7.72/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.50  
% 7.72/1.50  fof(f55,plain,(
% 7.72/1.50    v1_xboole_0(k1_xboole_0)),
% 7.72/1.50    inference(cnf_transformation,[],[f2])).
% 7.72/1.50  
% 7.72/1.50  fof(f14,axiom,(
% 7.72/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 7.72/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.50  
% 7.72/1.50  fof(f33,plain,(
% 7.72/1.50    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.72/1.50    inference(ennf_transformation,[],[f14])).
% 7.72/1.50  
% 7.72/1.50  fof(f34,plain,(
% 7.72/1.50    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.72/1.50    inference(flattening,[],[f33])).
% 7.72/1.50  
% 7.72/1.50  fof(f77,plain,(
% 7.72/1.50    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.72/1.50    inference(cnf_transformation,[],[f34])).
% 7.72/1.50  
% 7.72/1.50  fof(f75,plain,(
% 7.72/1.50    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.72/1.50    inference(cnf_transformation,[],[f32])).
% 7.72/1.50  
% 7.72/1.50  fof(f6,axiom,(
% 7.72/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.72/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.50  
% 7.72/1.50  fof(f17,plain,(
% 7.72/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.72/1.50    inference(pure_predicate_removal,[],[f6])).
% 7.72/1.50  
% 7.72/1.50  fof(f21,plain,(
% 7.72/1.50    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.72/1.50    inference(ennf_transformation,[],[f17])).
% 7.72/1.50  
% 7.72/1.50  fof(f62,plain,(
% 7.72/1.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.72/1.50    inference(cnf_transformation,[],[f21])).
% 7.72/1.50  
% 7.72/1.50  fof(f11,axiom,(
% 7.72/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 7.72/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.50  
% 7.72/1.50  fof(f27,plain,(
% 7.72/1.50    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.72/1.50    inference(ennf_transformation,[],[f11])).
% 7.72/1.50  
% 7.72/1.50  fof(f28,plain,(
% 7.72/1.50    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.72/1.50    inference(flattening,[],[f27])).
% 7.72/1.50  
% 7.72/1.50  fof(f72,plain,(
% 7.72/1.50    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.72/1.50    inference(cnf_transformation,[],[f28])).
% 7.72/1.50  
% 7.72/1.50  fof(f82,plain,(
% 7.72/1.50    v1_funct_1(sK8)),
% 7.72/1.50    inference(cnf_transformation,[],[f52])).
% 7.72/1.50  
% 7.72/1.50  fof(f86,plain,(
% 7.72/1.50    k1_xboole_0 != sK5),
% 7.72/1.50    inference(cnf_transformation,[],[f52])).
% 7.72/1.50  
% 7.72/1.50  fof(f87,plain,(
% 7.72/1.50    k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9)),
% 7.72/1.50    inference(cnf_transformation,[],[f52])).
% 7.72/1.50  
% 7.72/1.50  fof(f12,axiom,(
% 7.72/1.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 7.72/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.50  
% 7.72/1.50  fof(f29,plain,(
% 7.72/1.50    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 7.72/1.50    inference(ennf_transformation,[],[f12])).
% 7.72/1.50  
% 7.72/1.50  fof(f30,plain,(
% 7.72/1.50    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 7.72/1.50    inference(flattening,[],[f29])).
% 7.72/1.50  
% 7.72/1.50  fof(f73,plain,(
% 7.72/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 7.72/1.50    inference(cnf_transformation,[],[f30])).
% 7.72/1.50  
% 7.72/1.50  fof(f4,axiom,(
% 7.72/1.50    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 7.72/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.50  
% 7.72/1.50  fof(f41,plain,(
% 7.72/1.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 7.72/1.50    inference(nnf_transformation,[],[f4])).
% 7.72/1.50  
% 7.72/1.50  fof(f42,plain,(
% 7.72/1.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 7.72/1.50    inference(rectify,[],[f41])).
% 7.72/1.50  
% 7.72/1.50  fof(f45,plain,(
% 7.72/1.50    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 7.72/1.50    introduced(choice_axiom,[])).
% 7.72/1.50  
% 7.72/1.50  fof(f44,plain,(
% 7.72/1.50    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 7.72/1.50    introduced(choice_axiom,[])).
% 7.72/1.50  
% 7.72/1.50  fof(f43,plain,(
% 7.72/1.50    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 7.72/1.50    introduced(choice_axiom,[])).
% 7.72/1.50  
% 7.72/1.50  fof(f46,plain,(
% 7.72/1.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 7.72/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f42,f45,f44,f43])).
% 7.72/1.50  
% 7.72/1.50  fof(f59,plain,(
% 7.72/1.50    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 7.72/1.50    inference(cnf_transformation,[],[f46])).
% 7.72/1.50  
% 7.72/1.50  fof(f58,plain,(
% 7.72/1.50    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 7.72/1.50    inference(cnf_transformation,[],[f46])).
% 7.72/1.50  
% 7.72/1.50  fof(f88,plain,(
% 7.72/1.50    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 7.72/1.50    inference(equality_resolution,[],[f58])).
% 7.72/1.50  
% 7.72/1.50  fof(f1,axiom,(
% 7.72/1.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.72/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.50  
% 7.72/1.50  fof(f37,plain,(
% 7.72/1.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.72/1.50    inference(nnf_transformation,[],[f1])).
% 7.72/1.50  
% 7.72/1.50  fof(f38,plain,(
% 7.72/1.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.72/1.50    inference(rectify,[],[f37])).
% 7.72/1.50  
% 7.72/1.50  fof(f39,plain,(
% 7.72/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.72/1.50    introduced(choice_axiom,[])).
% 7.72/1.50  
% 7.72/1.50  fof(f40,plain,(
% 7.72/1.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.72/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 7.72/1.50  
% 7.72/1.50  fof(f53,plain,(
% 7.72/1.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.72/1.50    inference(cnf_transformation,[],[f40])).
% 7.72/1.50  
% 7.72/1.50  fof(f57,plain,(
% 7.72/1.50    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 7.72/1.50    inference(cnf_transformation,[],[f46])).
% 7.72/1.50  
% 7.72/1.50  fof(f89,plain,(
% 7.72/1.50    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 7.72/1.50    inference(equality_resolution,[],[f57])).
% 7.72/1.50  
% 7.72/1.50  fof(f7,axiom,(
% 7.72/1.50    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 7.72/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.50  
% 7.72/1.50  fof(f22,plain,(
% 7.72/1.50    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 7.72/1.50    inference(ennf_transformation,[],[f7])).
% 7.72/1.50  
% 7.72/1.50  fof(f63,plain,(
% 7.72/1.50    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 7.72/1.50    inference(cnf_transformation,[],[f22])).
% 7.72/1.50  
% 7.72/1.50  cnf(c_28,negated_conjecture,
% 7.72/1.50      ( m1_subset_1(sK9,sK5) ),
% 7.72/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2044,plain,
% 7.72/1.50      ( m1_subset_1(sK9,sK5) = iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_3,plain,
% 7.72/1.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.72/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2060,plain,
% 7.72/1.50      ( m1_subset_1(X0,X1) != iProver_top
% 7.72/1.50      | r2_hidden(X0,X1) = iProver_top
% 7.72/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_3586,plain,
% 7.72/1.50      ( r2_hidden(sK9,sK5) = iProver_top
% 7.72/1.50      | v1_xboole_0(sK5) = iProver_top ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_2044,c_2060]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_31,negated_conjecture,
% 7.72/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 7.72/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2041,plain,
% 7.72/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_12,plain,
% 7.72/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.72/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.72/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2052,plain,
% 7.72/1.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.72/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2950,plain,
% 7.72/1.50      ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_2041,c_2052]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_21,plain,
% 7.72/1.50      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.72/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.72/1.50      | ~ v1_funct_1(X0)
% 7.72/1.50      | ~ v1_relat_1(X0) ),
% 7.72/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_27,negated_conjecture,
% 7.72/1.50      ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) ),
% 7.72/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_485,plain,
% 7.72/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.72/1.50      | ~ v1_funct_1(X0)
% 7.72/1.50      | ~ v1_relat_1(X0)
% 7.72/1.50      | k2_relset_1(sK5,sK6,sK7) != k2_relat_1(X0)
% 7.72/1.50      | k1_relset_1(sK6,sK4,sK8) != X1 ),
% 7.72/1.50      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_486,plain,
% 7.72/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relset_1(sK6,sK4,sK8))))
% 7.72/1.50      | ~ v1_funct_1(X0)
% 7.72/1.50      | ~ v1_relat_1(X0)
% 7.72/1.50      | k2_relset_1(sK5,sK6,sK7) != k2_relat_1(X0) ),
% 7.72/1.50      inference(unflattening,[status(thm)],[c_485]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2034,plain,
% 7.72/1.50      ( k2_relset_1(sK5,sK6,sK7) != k2_relat_1(X0)
% 7.72/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relset_1(sK6,sK4,sK8)))) = iProver_top
% 7.72/1.50      | v1_funct_1(X0) != iProver_top
% 7.72/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_3216,plain,
% 7.72/1.50      ( k2_relat_1(X0) != k2_relat_1(sK7)
% 7.72/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relset_1(sK6,sK4,sK8)))) = iProver_top
% 7.72/1.50      | v1_funct_1(X0) != iProver_top
% 7.72/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.50      inference(demodulation,[status(thm)],[c_2950,c_2034]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_29,negated_conjecture,
% 7.72/1.50      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
% 7.72/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2043,plain,
% 7.72/1.50      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_11,plain,
% 7.72/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.72/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.72/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2053,plain,
% 7.72/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.72/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2952,plain,
% 7.72/1.50      ( k1_relset_1(sK6,sK4,sK8) = k1_relat_1(sK8) ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_2043,c_2053]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_3217,plain,
% 7.72/1.50      ( k2_relat_1(X0) != k2_relat_1(sK7)
% 7.72/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relat_1(sK8)))) = iProver_top
% 7.72/1.50      | v1_funct_1(X0) != iProver_top
% 7.72/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.50      inference(light_normalisation,[status(thm)],[c_3216,c_2952]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_4434,plain,
% 7.72/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k1_relat_1(sK8)))) = iProver_top
% 7.72/1.50      | v1_funct_1(sK7) != iProver_top
% 7.72/1.50      | v1_relat_1(sK7) != iProver_top ),
% 7.72/1.50      inference(equality_resolution,[status(thm)],[c_3217]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_33,negated_conjecture,
% 7.72/1.50      ( v1_funct_1(sK7) ),
% 7.72/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_36,plain,
% 7.72/1.50      ( v1_funct_1(sK7) = iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_38,plain,
% 7.72/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_8,plain,
% 7.72/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.72/1.50      | v1_relat_1(X0) ),
% 7.72/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2178,plain,
% 7.72/1.50      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.72/1.50      | v1_relat_1(sK7) ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2383,plain,
% 7.72/1.50      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 7.72/1.50      | v1_relat_1(sK7) ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_2178]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2384,plain,
% 7.72/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 7.72/1.50      | v1_relat_1(sK7) = iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_2383]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_6396,plain,
% 7.72/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k1_relat_1(sK8)))) = iProver_top ),
% 7.72/1.50      inference(global_propositional_subsumption,
% 7.72/1.50                [status(thm)],
% 7.72/1.50                [c_4434,c_36,c_38,c_2384]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_18,plain,
% 7.72/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.72/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.72/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.72/1.50      | k1_xboole_0 = X2 ),
% 7.72/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2046,plain,
% 7.72/1.50      ( k1_relset_1(X0,X1,X2) = X0
% 7.72/1.50      | k1_xboole_0 = X1
% 7.72/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.72/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_4078,plain,
% 7.72/1.50      ( k1_relset_1(sK5,sK6,sK7) = sK5
% 7.72/1.50      | sK6 = k1_xboole_0
% 7.72/1.50      | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_2041,c_2046]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2953,plain,
% 7.72/1.50      ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_2041,c_2053]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_4079,plain,
% 7.72/1.50      ( k1_relat_1(sK7) = sK5
% 7.72/1.50      | sK6 = k1_xboole_0
% 7.72/1.50      | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
% 7.72/1.50      inference(demodulation,[status(thm)],[c_4078,c_2953]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_34,negated_conjecture,
% 7.72/1.50      ( ~ v1_xboole_0(sK6) ),
% 7.72/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_32,negated_conjecture,
% 7.72/1.50      ( v1_funct_2(sK7,sK5,sK6) ),
% 7.72/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_37,plain,
% 7.72/1.50      ( v1_funct_2(sK7,sK5,sK6) = iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2,plain,
% 7.72/1.50      ( v1_xboole_0(k1_xboole_0) ),
% 7.72/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_1532,plain,
% 7.72/1.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.72/1.50      theory(equality) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2137,plain,
% 7.72/1.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK6) | sK6 != X0 ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_1532]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2144,plain,
% 7.72/1.50      ( v1_xboole_0(sK6)
% 7.72/1.50      | ~ v1_xboole_0(k1_xboole_0)
% 7.72/1.50      | sK6 != k1_xboole_0 ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_2137]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_4498,plain,
% 7.72/1.50      ( k1_relat_1(sK7) = sK5 ),
% 7.72/1.50      inference(global_propositional_subsumption,
% 7.72/1.50                [status(thm)],
% 7.72/1.50                [c_4079,c_34,c_37,c_2,c_2144]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_6400,plain,
% 7.72/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK8)))) = iProver_top ),
% 7.72/1.50      inference(light_normalisation,[status(thm)],[c_6396,c_4498]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_24,plain,
% 7.72/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.72/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.72/1.50      | ~ r2_hidden(X3,X1)
% 7.72/1.50      | r2_hidden(k1_funct_1(X0,X3),X2)
% 7.72/1.50      | ~ v1_funct_1(X0)
% 7.72/1.50      | k1_xboole_0 = X2 ),
% 7.72/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2045,plain,
% 7.72/1.50      ( k1_xboole_0 = X0
% 7.72/1.50      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.72/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.72/1.50      | r2_hidden(X3,X2) != iProver_top
% 7.72/1.50      | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
% 7.72/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_6405,plain,
% 7.72/1.50      ( k1_relat_1(sK8) = k1_xboole_0
% 7.72/1.50      | v1_funct_2(sK7,sK5,k1_relat_1(sK8)) != iProver_top
% 7.72/1.50      | r2_hidden(X0,sK5) != iProver_top
% 7.72/1.50      | r2_hidden(k1_funct_1(sK7,X0),k1_relat_1(sK8)) = iProver_top
% 7.72/1.50      | v1_funct_1(sK7) != iProver_top ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_6400,c_2045]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_22,plain,
% 7.72/1.50      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 7.72/1.50      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.72/1.50      | ~ v1_funct_1(X0)
% 7.72/1.50      | ~ v1_relat_1(X0) ),
% 7.72/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_467,plain,
% 7.72/1.50      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 7.72/1.50      | ~ v1_funct_1(X0)
% 7.72/1.50      | ~ v1_relat_1(X0)
% 7.72/1.50      | k2_relset_1(sK5,sK6,sK7) != k2_relat_1(X0)
% 7.72/1.50      | k1_relset_1(sK6,sK4,sK8) != X1 ),
% 7.72/1.50      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_468,plain,
% 7.72/1.50      ( v1_funct_2(X0,k1_relat_1(X0),k1_relset_1(sK6,sK4,sK8))
% 7.72/1.50      | ~ v1_funct_1(X0)
% 7.72/1.50      | ~ v1_relat_1(X0)
% 7.72/1.50      | k2_relset_1(sK5,sK6,sK7) != k2_relat_1(X0) ),
% 7.72/1.50      inference(unflattening,[status(thm)],[c_467]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2035,plain,
% 7.72/1.50      ( k2_relset_1(sK5,sK6,sK7) != k2_relat_1(X0)
% 7.72/1.50      | v1_funct_2(X0,k1_relat_1(X0),k1_relset_1(sK6,sK4,sK8)) = iProver_top
% 7.72/1.50      | v1_funct_1(X0) != iProver_top
% 7.72/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_3215,plain,
% 7.72/1.50      ( k2_relat_1(X0) != k2_relat_1(sK7)
% 7.72/1.50      | v1_funct_2(X0,k1_relat_1(X0),k1_relset_1(sK6,sK4,sK8)) = iProver_top
% 7.72/1.50      | v1_funct_1(X0) != iProver_top
% 7.72/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.50      inference(demodulation,[status(thm)],[c_2950,c_2035]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_3218,plain,
% 7.72/1.50      ( k2_relat_1(X0) != k2_relat_1(sK7)
% 7.72/1.50      | v1_funct_2(X0,k1_relat_1(X0),k1_relat_1(sK8)) = iProver_top
% 7.72/1.50      | v1_funct_1(X0) != iProver_top
% 7.72/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.50      inference(light_normalisation,[status(thm)],[c_3215,c_2952]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_4366,plain,
% 7.72/1.50      ( v1_funct_2(sK7,k1_relat_1(sK7),k1_relat_1(sK8)) = iProver_top
% 7.72/1.50      | v1_funct_1(sK7) != iProver_top
% 7.72/1.50      | v1_relat_1(sK7) != iProver_top ),
% 7.72/1.50      inference(equality_resolution,[status(thm)],[c_3218]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_6328,plain,
% 7.72/1.50      ( v1_funct_2(sK7,k1_relat_1(sK7),k1_relat_1(sK8)) = iProver_top ),
% 7.72/1.50      inference(global_propositional_subsumption,
% 7.72/1.50                [status(thm)],
% 7.72/1.50                [c_4366,c_36,c_38,c_2384]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_6332,plain,
% 7.72/1.50      ( v1_funct_2(sK7,sK5,k1_relat_1(sK8)) = iProver_top ),
% 7.72/1.50      inference(light_normalisation,[status(thm)],[c_6328,c_4498]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_21905,plain,
% 7.72/1.50      ( r2_hidden(k1_funct_1(sK7,X0),k1_relat_1(sK8)) = iProver_top
% 7.72/1.50      | r2_hidden(X0,sK5) != iProver_top
% 7.72/1.50      | k1_relat_1(sK8) = k1_xboole_0 ),
% 7.72/1.50      inference(global_propositional_subsumption,
% 7.72/1.50                [status(thm)],
% 7.72/1.50                [c_6405,c_36,c_6332]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_21906,plain,
% 7.72/1.50      ( k1_relat_1(sK8) = k1_xboole_0
% 7.72/1.50      | r2_hidden(X0,sK5) != iProver_top
% 7.72/1.50      | r2_hidden(k1_funct_1(sK7,X0),k1_relat_1(sK8)) = iProver_top ),
% 7.72/1.50      inference(renaming,[status(thm)],[c_21905]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_9,plain,
% 7.72/1.50      ( v5_relat_1(X0,X1)
% 7.72/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.72/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_19,plain,
% 7.72/1.50      ( ~ v5_relat_1(X0,X1)
% 7.72/1.50      | ~ r2_hidden(X2,k1_relat_1(X0))
% 7.72/1.50      | ~ v1_funct_1(X0)
% 7.72/1.50      | ~ v1_relat_1(X0)
% 7.72/1.50      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 7.72/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_361,plain,
% 7.72/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.72/1.50      | ~ r2_hidden(X3,k1_relat_1(X0))
% 7.72/1.50      | ~ v1_funct_1(X0)
% 7.72/1.50      | ~ v1_relat_1(X0)
% 7.72/1.50      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.72/1.50      inference(resolution,[status(thm)],[c_9,c_19]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_365,plain,
% 7.72/1.50      ( ~ v1_funct_1(X0)
% 7.72/1.50      | ~ r2_hidden(X3,k1_relat_1(X0))
% 7.72/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.72/1.50      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.72/1.50      inference(global_propositional_subsumption,
% 7.72/1.50                [status(thm)],
% 7.72/1.50                [c_361,c_8]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_366,plain,
% 7.72/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.72/1.50      | ~ r2_hidden(X3,k1_relat_1(X0))
% 7.72/1.50      | ~ v1_funct_1(X0)
% 7.72/1.50      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.72/1.50      inference(renaming,[status(thm)],[c_365]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2037,plain,
% 7.72/1.50      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 7.72/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 7.72/1.50      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 7.72/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2900,plain,
% 7.72/1.50      ( k7_partfun1(sK4,sK8,X0) = k1_funct_1(sK8,X0)
% 7.72/1.50      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 7.72/1.50      | v1_funct_1(sK8) != iProver_top ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_2043,c_2037]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_30,negated_conjecture,
% 7.72/1.50      ( v1_funct_1(sK8) ),
% 7.72/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_39,plain,
% 7.72/1.50      ( v1_funct_1(sK8) = iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_3321,plain,
% 7.72/1.50      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 7.72/1.50      | k7_partfun1(sK4,sK8,X0) = k1_funct_1(sK8,X0) ),
% 7.72/1.50      inference(global_propositional_subsumption,
% 7.72/1.50                [status(thm)],
% 7.72/1.50                [c_2900,c_39]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_3322,plain,
% 7.72/1.50      ( k7_partfun1(sK4,sK8,X0) = k1_funct_1(sK8,X0)
% 7.72/1.50      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
% 7.72/1.50      inference(renaming,[status(thm)],[c_3321]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_21913,plain,
% 7.72/1.50      ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,X0)) = k1_funct_1(sK8,k1_funct_1(sK7,X0))
% 7.72/1.50      | k1_relat_1(sK8) = k1_xboole_0
% 7.72/1.50      | r2_hidden(X0,sK5) != iProver_top ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_21906,c_3322]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_22118,plain,
% 7.72/1.50      ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9))
% 7.72/1.50      | k1_relat_1(sK8) = k1_xboole_0
% 7.72/1.50      | v1_xboole_0(sK5) = iProver_top ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_3586,c_21913]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_26,negated_conjecture,
% 7.72/1.50      ( k1_xboole_0 != sK5 ),
% 7.72/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_25,negated_conjecture,
% 7.72/1.50      ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) ),
% 7.72/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_105,plain,
% 7.72/1.50      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_1530,plain,( X0 = X0 ),theory(equality) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_1559,plain,
% 7.72/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_1530]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_1531,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2127,plain,
% 7.72/1.50      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_1531]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2128,plain,
% 7.72/1.50      ( sK5 != k1_xboole_0
% 7.72/1.50      | k1_xboole_0 = sK5
% 7.72/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_2127]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2104,plain,
% 7.72/1.50      ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != X0
% 7.72/1.50      | k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9)
% 7.72/1.50      | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != X0 ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_1531]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2187,plain,
% 7.72/1.50      ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9)
% 7.72/1.50      | k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
% 7.72/1.50      | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_2104]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_20,plain,
% 7.72/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.72/1.50      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 7.72/1.50      | ~ m1_subset_1(X5,X1)
% 7.72/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.72/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.72/1.50      | ~ v1_funct_1(X4)
% 7.72/1.50      | ~ v1_funct_1(X0)
% 7.72/1.50      | v1_xboole_0(X2)
% 7.72/1.50      | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k1_funct_1(X4,k1_funct_1(X0,X5))
% 7.72/1.50      | k1_xboole_0 = X1 ),
% 7.72/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_431,plain,
% 7.72/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.72/1.50      | ~ m1_subset_1(X3,X1)
% 7.72/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.72/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 7.72/1.50      | ~ v1_funct_1(X0)
% 7.72/1.50      | ~ v1_funct_1(X4)
% 7.72/1.50      | v1_xboole_0(X2)
% 7.72/1.50      | k2_relset_1(X1,X2,X0) != k2_relset_1(sK5,sK6,sK7)
% 7.72/1.50      | k1_relset_1(X2,X5,X4) != k1_relset_1(sK6,sK4,sK8)
% 7.72/1.50      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 7.72/1.50      | k1_xboole_0 = X1 ),
% 7.72/1.50      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2036,plain,
% 7.72/1.50      ( k2_relset_1(X0,X1,X2) != k2_relset_1(sK5,sK6,sK7)
% 7.72/1.50      | k1_relset_1(X1,X3,X4) != k1_relset_1(sK6,sK4,sK8)
% 7.72/1.50      | k1_funct_1(k8_funct_2(X0,X1,X3,X2,X4),X5) = k1_funct_1(X4,k1_funct_1(X2,X5))
% 7.72/1.50      | k1_xboole_0 = X0
% 7.72/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.72/1.50      | m1_subset_1(X5,X0) != iProver_top
% 7.72/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.72/1.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 7.72/1.50      | v1_funct_1(X2) != iProver_top
% 7.72/1.50      | v1_funct_1(X4) != iProver_top
% 7.72/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2690,plain,
% 7.72/1.50      ( k1_relset_1(sK6,X0,X1) != k1_relset_1(sK6,sK4,sK8)
% 7.72/1.50      | k1_funct_1(k8_funct_2(sK5,sK6,X0,sK7,X1),X2) = k1_funct_1(X1,k1_funct_1(sK7,X2))
% 7.72/1.50      | sK5 = k1_xboole_0
% 7.72/1.50      | v1_funct_2(sK7,sK5,sK6) != iProver_top
% 7.72/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) != iProver_top
% 7.72/1.50      | m1_subset_1(X2,sK5) != iProver_top
% 7.72/1.50      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 7.72/1.50      | v1_funct_1(X1) != iProver_top
% 7.72/1.50      | v1_funct_1(sK7) != iProver_top
% 7.72/1.50      | v1_xboole_0(sK6) = iProver_top ),
% 7.72/1.50      inference(equality_resolution,[status(thm)],[c_2036]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_35,plain,
% 7.72/1.50      ( v1_xboole_0(sK6) != iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2695,plain,
% 7.72/1.50      ( m1_subset_1(X2,sK5) != iProver_top
% 7.72/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) != iProver_top
% 7.72/1.50      | k1_funct_1(k8_funct_2(sK5,sK6,X0,sK7,X1),X2) = k1_funct_1(X1,k1_funct_1(sK7,X2))
% 7.72/1.50      | k1_relset_1(sK6,X0,X1) != k1_relset_1(sK6,sK4,sK8)
% 7.72/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.72/1.50      inference(global_propositional_subsumption,
% 7.72/1.50                [status(thm)],
% 7.72/1.50                [c_2690,c_35,c_36,c_37,c_38,c_26,c_1559,c_2128]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2696,plain,
% 7.72/1.50      ( k1_relset_1(sK6,X0,X1) != k1_relset_1(sK6,sK4,sK8)
% 7.72/1.50      | k1_funct_1(k8_funct_2(sK5,sK6,X0,sK7,X1),X2) = k1_funct_1(X1,k1_funct_1(sK7,X2))
% 7.72/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) != iProver_top
% 7.72/1.50      | m1_subset_1(X2,sK5) != iProver_top
% 7.72/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.72/1.50      inference(renaming,[status(thm)],[c_2695]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2701,plain,
% 7.72/1.50      ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),X0) = k1_funct_1(sK8,k1_funct_1(sK7,X0))
% 7.72/1.50      | m1_subset_1(X0,sK5) != iProver_top
% 7.72/1.50      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) != iProver_top
% 7.72/1.50      | v1_funct_1(sK8) != iProver_top ),
% 7.72/1.50      inference(equality_resolution,[status(thm)],[c_2696]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_40,plain,
% 7.72/1.50      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2808,plain,
% 7.72/1.50      ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),X0) = k1_funct_1(sK8,k1_funct_1(sK7,X0))
% 7.72/1.50      | m1_subset_1(X0,sK5) != iProver_top ),
% 7.72/1.50      inference(global_propositional_subsumption,
% 7.72/1.50                [status(thm)],
% 7.72/1.50                [c_2701,c_39,c_40]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2814,plain,
% 7.72/1.50      ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) = k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_2044,c_2808]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_5,plain,
% 7.72/1.50      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
% 7.72/1.50      | r2_hidden(sK1(X0,X1),X1)
% 7.72/1.50      | k1_relat_1(X0) = X1 ),
% 7.72/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2058,plain,
% 7.72/1.50      ( k1_relat_1(X0) = X1
% 7.72/1.50      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) = iProver_top
% 7.72/1.50      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_6,plain,
% 7.72/1.50      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 7.72/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2057,plain,
% 7.72/1.50      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 7.72/1.50      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_4192,plain,
% 7.72/1.50      ( k1_relat_1(X0) = X1
% 7.72/1.50      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 7.72/1.50      | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_2058,c_2057]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_9460,plain,
% 7.72/1.50      ( k1_relat_1(sK7) = X0
% 7.72/1.50      | r2_hidden(sK1(sK7,X0),X0) = iProver_top
% 7.72/1.50      | r2_hidden(sK1(sK7,X0),sK5) = iProver_top ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_4498,c_4192]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_9491,plain,
% 7.72/1.50      ( sK5 = X0
% 7.72/1.50      | r2_hidden(sK1(sK7,X0),X0) = iProver_top
% 7.72/1.50      | r2_hidden(sK1(sK7,X0),sK5) = iProver_top ),
% 7.72/1.50      inference(demodulation,[status(thm)],[c_9460,c_4498]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_1,plain,
% 7.72/1.50      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.72/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2062,plain,
% 7.72/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.72/1.50      | v1_xboole_0(X1) != iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_9661,plain,
% 7.72/1.50      ( sK5 = X0
% 7.72/1.50      | r2_hidden(sK1(sK7,X0),X0) = iProver_top
% 7.72/1.50      | v1_xboole_0(sK5) != iProver_top ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_9491,c_2062]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_10176,plain,
% 7.72/1.50      ( sK5 = X0
% 7.72/1.50      | v1_xboole_0(X0) != iProver_top
% 7.72/1.50      | v1_xboole_0(sK5) != iProver_top ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_9661,c_2062]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_10192,plain,
% 7.72/1.50      ( sK5 = k1_xboole_0
% 7.72/1.50      | v1_xboole_0(sK5) != iProver_top
% 7.72/1.50      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_10176]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_22208,plain,
% 7.72/1.50      ( k1_relat_1(sK8) = k1_xboole_0 ),
% 7.72/1.50      inference(global_propositional_subsumption,
% 7.72/1.50                [status(thm)],
% 7.72/1.50                [c_22118,c_26,c_25,c_105,c_1559,c_2128,c_2187,c_2814,
% 7.72/1.50                 c_10192]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_21911,plain,
% 7.72/1.50      ( k1_relat_1(sK8) = k1_xboole_0
% 7.72/1.50      | r2_hidden(X0,sK5) != iProver_top
% 7.72/1.50      | v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_21906,c_2062]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2842,plain,
% 7.72/1.50      ( sK5 = sK5 ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_1530]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_3958,plain,
% 7.72/1.50      ( X0 != X1 | X0 = k1_relat_1(X2) | k1_relat_1(X2) != X1 ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_1531]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_3959,plain,
% 7.72/1.50      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 7.72/1.50      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 7.72/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_3958]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2189,plain,
% 7.72/1.50      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_1531]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2424,plain,
% 7.72/1.50      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_2189]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_4183,plain,
% 7.72/1.50      ( k1_relat_1(X0) != sK5 | sK5 = k1_relat_1(X0) | sK5 != sK5 ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_2424]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_4184,plain,
% 7.72/1.50      ( k1_relat_1(k1_xboole_0) != sK5
% 7.72/1.50      | sK5 = k1_relat_1(k1_xboole_0)
% 7.72/1.50      | sK5 != sK5 ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_4183]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_4191,plain,
% 7.72/1.50      ( k1_relat_1(X0) = X1
% 7.72/1.50      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 7.72/1.50      | v1_xboole_0(X0) != iProver_top ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_2058,c_2062]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_5746,plain,
% 7.72/1.50      ( k1_relat_1(X0) = X1
% 7.72/1.50      | v1_xboole_0(X1) != iProver_top
% 7.72/1.50      | v1_xboole_0(X0) != iProver_top ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_4191,c_2062]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_5757,plain,
% 7.72/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 7.72/1.50      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_5746]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_7,plain,
% 7.72/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.72/1.50      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
% 7.72/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2056,plain,
% 7.72/1.50      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.72/1.50      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2991,plain,
% 7.72/1.50      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.72/1.50      | v1_xboole_0(X1) != iProver_top ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_2056,c_2062]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_4645,plain,
% 7.72/1.50      ( r2_hidden(X0,sK5) != iProver_top
% 7.72/1.50      | v1_xboole_0(sK7) != iProver_top ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_4498,c_2991]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_5748,plain,
% 7.72/1.50      ( k1_relat_1(X0) = sK5
% 7.72/1.50      | v1_xboole_0(X0) != iProver_top
% 7.72/1.50      | v1_xboole_0(sK7) != iProver_top ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_4191,c_4645]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_5763,plain,
% 7.72/1.50      ( k1_relat_1(k1_xboole_0) = sK5
% 7.72/1.50      | v1_xboole_0(sK7) != iProver_top
% 7.72/1.50      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_5748]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_10,plain,
% 7.72/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.72/1.50      | ~ v1_xboole_0(X2)
% 7.72/1.50      | v1_xboole_0(X0) ),
% 7.72/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_2054,plain,
% 7.72/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.72/1.50      | v1_xboole_0(X2) != iProver_top
% 7.72/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.72/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_6403,plain,
% 7.72/1.50      ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top
% 7.72/1.50      | v1_xboole_0(sK7) = iProver_top ),
% 7.72/1.50      inference(superposition,[status(thm)],[c_6400,c_2054]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_7761,plain,
% 7.72/1.50      ( X0 != k1_relat_1(X1) | sK5 = X0 | sK5 != k1_relat_1(X1) ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_2189]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_7762,plain,
% 7.72/1.50      ( sK5 != k1_relat_1(k1_xboole_0)
% 7.72/1.50      | sK5 = k1_xboole_0
% 7.72/1.50      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 7.72/1.50      inference(instantiation,[status(thm)],[c_7761]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_21952,plain,
% 7.72/1.50      ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
% 7.72/1.50      inference(global_propositional_subsumption,
% 7.72/1.50                [status(thm)],
% 7.72/1.50                [c_21911,c_26,c_105,c_1559,c_2128,c_2842,c_3959,c_4184,
% 7.72/1.50                 c_5757,c_5763,c_6403,c_7762]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(c_22211,plain,
% 7.72/1.50      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.72/1.50      inference(demodulation,[status(thm)],[c_22208,c_21952]) ).
% 7.72/1.50  
% 7.72/1.50  cnf(contradiction,plain,
% 7.72/1.50      ( $false ),
% 7.72/1.50      inference(minisat,[status(thm)],[c_22211,c_105]) ).
% 7.72/1.50  
% 7.72/1.50  
% 7.72/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.72/1.50  
% 7.72/1.50  ------                               Statistics
% 7.72/1.50  
% 7.72/1.50  ------ General
% 7.72/1.50  
% 7.72/1.50  abstr_ref_over_cycles:                  0
% 7.72/1.50  abstr_ref_under_cycles:                 0
% 7.72/1.50  gc_basic_clause_elim:                   0
% 7.72/1.50  forced_gc_time:                         0
% 7.72/1.50  parsing_time:                           0.01
% 7.72/1.50  unif_index_cands_time:                  0.
% 7.72/1.50  unif_index_add_time:                    0.
% 7.72/1.50  orderings_time:                         0.
% 7.72/1.50  out_proof_time:                         0.015
% 7.72/1.50  total_time:                             0.859
% 7.72/1.50  num_of_symbols:                         60
% 7.72/1.50  num_of_terms:                           26333
% 7.72/1.50  
% 7.72/1.50  ------ Preprocessing
% 7.72/1.50  
% 7.72/1.50  num_of_splits:                          0
% 7.72/1.50  num_of_split_atoms:                     0
% 7.72/1.50  num_of_reused_defs:                     0
% 7.72/1.50  num_eq_ax_congr_red:                    32
% 7.72/1.50  num_of_sem_filtered_clauses:            1
% 7.72/1.50  num_of_subtypes:                        0
% 7.72/1.50  monotx_restored_types:                  0
% 7.72/1.50  sat_num_of_epr_types:                   0
% 7.72/1.50  sat_num_of_non_cyclic_types:            0
% 7.72/1.50  sat_guarded_non_collapsed_types:        0
% 7.72/1.50  num_pure_diseq_elim:                    0
% 7.72/1.50  simp_replaced_by:                       0
% 7.72/1.50  res_preprocessed:                       161
% 7.72/1.50  prep_upred:                             0
% 7.72/1.50  prep_unflattend:                        118
% 7.72/1.50  smt_new_axioms:                         0
% 7.72/1.50  pred_elim_cands:                        6
% 7.72/1.50  pred_elim:                              2
% 7.72/1.50  pred_elim_cl:                           2
% 7.72/1.50  pred_elim_cycles:                       7
% 7.72/1.50  merged_defs:                            0
% 7.72/1.50  merged_defs_ncl:                        0
% 7.72/1.50  bin_hyper_res:                          0
% 7.72/1.50  prep_cycles:                            4
% 7.72/1.50  pred_elim_time:                         0.032
% 7.72/1.50  splitting_time:                         0.
% 7.72/1.50  sem_filter_time:                        0.
% 7.72/1.50  monotx_time:                            0.001
% 7.72/1.50  subtype_inf_time:                       0.
% 7.72/1.50  
% 7.72/1.50  ------ Problem properties
% 7.72/1.50  
% 7.72/1.50  clauses:                                32
% 7.72/1.50  conjectures:                            9
% 7.72/1.50  epr:                                    9
% 7.72/1.50  horn:                                   23
% 7.72/1.50  ground:                                 10
% 7.72/1.50  unary:                                  10
% 7.72/1.50  binary:                                 7
% 7.72/1.50  lits:                                   86
% 7.72/1.50  lits_eq:                                23
% 7.72/1.50  fd_pure:                                0
% 7.72/1.50  fd_pseudo:                              0
% 7.72/1.50  fd_cond:                                5
% 7.72/1.50  fd_pseudo_cond:                         2
% 7.72/1.50  ac_symbols:                             0
% 7.72/1.50  
% 7.72/1.50  ------ Propositional Solver
% 7.72/1.50  
% 7.72/1.50  prop_solver_calls:                      35
% 7.72/1.50  prop_fast_solver_calls:                 2193
% 7.72/1.50  smt_solver_calls:                       0
% 7.72/1.50  smt_fast_solver_calls:                  0
% 7.72/1.50  prop_num_of_clauses:                    10894
% 7.72/1.50  prop_preprocess_simplified:             14496
% 7.72/1.50  prop_fo_subsumed:                       136
% 7.72/1.50  prop_solver_time:                       0.
% 7.72/1.50  smt_solver_time:                        0.
% 7.72/1.50  smt_fast_solver_time:                   0.
% 7.72/1.50  prop_fast_solver_time:                  0.
% 7.72/1.50  prop_unsat_core_time:                   0.001
% 7.72/1.50  
% 7.72/1.50  ------ QBF
% 7.72/1.50  
% 7.72/1.50  qbf_q_res:                              0
% 7.72/1.50  qbf_num_tautologies:                    0
% 7.72/1.50  qbf_prep_cycles:                        0
% 7.72/1.50  
% 7.72/1.50  ------ BMC1
% 7.72/1.50  
% 7.72/1.50  bmc1_current_bound:                     -1
% 7.72/1.50  bmc1_last_solved_bound:                 -1
% 7.72/1.50  bmc1_unsat_core_size:                   -1
% 7.72/1.50  bmc1_unsat_core_parents_size:           -1
% 7.72/1.50  bmc1_merge_next_fun:                    0
% 7.72/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.72/1.50  
% 7.72/1.50  ------ Instantiation
% 7.72/1.50  
% 7.72/1.50  inst_num_of_clauses:                    2319
% 7.72/1.50  inst_num_in_passive:                    592
% 7.72/1.50  inst_num_in_active:                     1332
% 7.72/1.50  inst_num_in_unprocessed:                395
% 7.72/1.50  inst_num_of_loops:                      1450
% 7.72/1.50  inst_num_of_learning_restarts:          0
% 7.72/1.50  inst_num_moves_active_passive:          112
% 7.72/1.50  inst_lit_activity:                      0
% 7.72/1.50  inst_lit_activity_moves:                0
% 7.72/1.50  inst_num_tautologies:                   0
% 7.72/1.50  inst_num_prop_implied:                  0
% 7.72/1.50  inst_num_existing_simplified:           0
% 7.72/1.50  inst_num_eq_res_simplified:             0
% 7.72/1.50  inst_num_child_elim:                    0
% 7.72/1.50  inst_num_of_dismatching_blockings:      336
% 7.72/1.50  inst_num_of_non_proper_insts:           2286
% 7.72/1.50  inst_num_of_duplicates:                 0
% 7.72/1.50  inst_inst_num_from_inst_to_res:         0
% 7.72/1.50  inst_dismatching_checking_time:         0.
% 7.72/1.50  
% 7.72/1.50  ------ Resolution
% 7.72/1.50  
% 7.72/1.50  res_num_of_clauses:                     0
% 7.72/1.50  res_num_in_passive:                     0
% 7.72/1.50  res_num_in_active:                      0
% 7.72/1.50  res_num_of_loops:                       165
% 7.72/1.50  res_forward_subset_subsumed:            139
% 7.72/1.50  res_backward_subset_subsumed:           0
% 7.72/1.50  res_forward_subsumed:                   2
% 7.72/1.50  res_backward_subsumed:                  0
% 7.72/1.50  res_forward_subsumption_resolution:     4
% 7.72/1.50  res_backward_subsumption_resolution:    0
% 7.72/1.50  res_clause_to_clause_subsumption:       8439
% 7.72/1.50  res_orphan_elimination:                 0
% 7.72/1.50  res_tautology_del:                      144
% 7.72/1.50  res_num_eq_res_simplified:              0
% 7.72/1.50  res_num_sel_changes:                    0
% 7.72/1.50  res_moves_from_active_to_pass:          0
% 7.72/1.50  
% 7.72/1.50  ------ Superposition
% 7.72/1.50  
% 7.72/1.50  sup_time_total:                         0.
% 7.72/1.50  sup_time_generating:                    0.
% 7.72/1.50  sup_time_sim_full:                      0.
% 7.72/1.50  sup_time_sim_immed:                     0.
% 7.72/1.50  
% 7.72/1.50  sup_num_of_clauses:                     1167
% 7.72/1.50  sup_num_in_active:                      141
% 7.72/1.50  sup_num_in_passive:                     1026
% 7.72/1.50  sup_num_of_loops:                       289
% 7.72/1.50  sup_fw_superposition:                   1447
% 7.72/1.50  sup_bw_superposition:                   1256
% 7.72/1.50  sup_immediate_simplified:               226
% 7.72/1.50  sup_given_eliminated:                   0
% 7.72/1.50  comparisons_done:                       0
% 7.72/1.50  comparisons_avoided:                    391
% 7.72/1.50  
% 7.72/1.50  ------ Simplifications
% 7.72/1.50  
% 7.72/1.50  
% 7.72/1.50  sim_fw_subset_subsumed:                 95
% 7.72/1.50  sim_bw_subset_subsumed:                 49
% 7.72/1.50  sim_fw_subsumed:                        52
% 7.72/1.50  sim_bw_subsumed:                        19
% 7.72/1.50  sim_fw_subsumption_res:                 0
% 7.72/1.50  sim_bw_subsumption_res:                 0
% 7.72/1.50  sim_tautology_del:                      34
% 7.72/1.50  sim_eq_tautology_del:                   68
% 7.72/1.50  sim_eq_res_simp:                        0
% 7.72/1.50  sim_fw_demodulated:                     15
% 7.72/1.50  sim_bw_demodulated:                     121
% 7.72/1.50  sim_light_normalised:                   157
% 7.72/1.50  sim_joinable_taut:                      0
% 7.72/1.50  sim_joinable_simp:                      0
% 7.72/1.50  sim_ac_normalised:                      0
% 7.72/1.50  sim_smt_subsumption:                    0
% 7.72/1.50  
%------------------------------------------------------------------------------

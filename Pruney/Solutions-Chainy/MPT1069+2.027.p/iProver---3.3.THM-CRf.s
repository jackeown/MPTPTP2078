%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:47 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :  189 (1621 expanded)
%              Number of clauses        :  119 ( 472 expanded)
%              Number of leaves         :   22 ( 539 expanded)
%              Depth                    :   26
%              Number of atoms          :  660 (11909 expanded)
%              Number of equality atoms :  311 (3373 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k7_partfun1(X0,X4,k1_funct_1(X3,sK5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5)
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
            ( k7_partfun1(X0,sK4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5)
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
                ( k7_partfun1(X0,X4,k1_funct_1(sK3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5)
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK3,X1,X2)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
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
                  ( k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5)
                  & k1_xboole_0 != sK1
                  & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5)
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f37,f42,f41,f40,f39])).

fof(f72,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

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
    inference(ennf_transformation,[],[f10])).

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

fof(f38,plain,(
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

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1913,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1925,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2957,plain,
    ( r2_hidden(sK5,sK1) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1913,c_1925])).

cnf(c_38,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2152,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2153,plain,
    ( k1_xboole_0 = sK1
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2152])).

cnf(c_2310,plain,
    ( ~ m1_subset_1(X0,sK1)
    | r2_hidden(X0,sK1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2520,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | r2_hidden(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2310])).

cnf(c_2521,plain,
    ( m1_subset_1(sK5,sK1) != iProver_top
    | r2_hidden(sK5,sK1) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2520])).

cnf(c_3864,plain,
    ( r2_hidden(sK5,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2957,c_38,c_23,c_2153,c_2521])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1910,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1921,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2853,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1910,c_1921])).

cnf(c_18,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_432,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0)
    | k1_relset_1(sK2,sK0,sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_433,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_1903,plain,
    ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_3126,plain,
    ( k2_relat_1(X0) != k2_relat_1(sK3)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2853,c_1903])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1912,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1922,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2861,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1912,c_1922])).

cnf(c_4099,plain,
    ( k2_relat_1(X0) != k2_relat_1(sK3)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3126,c_2861])).

cnf(c_4107,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4099])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_33,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_35,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2161,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2162,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2161])).

cnf(c_4867,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4107,c_33,c_35,c_2162])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1915,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4246,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1910,c_1915])).

cnf(c_2862,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1910,c_1922])).

cnf(c_4250,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4246,c_2862])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_34,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1450,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2164,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1450])).

cnf(c_2166,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2164])).

cnf(c_4585,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4250,c_31,c_34,c_0,c_2166])).

cnf(c_4871,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4867,c_4585])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1914,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4880,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(sK3,sK1,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4871,c_1914])).

cnf(c_19,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_414,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0)
    | k1_relset_1(sK2,sK0,sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_415,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_1904,plain,
    ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0)
    | v1_funct_2(X0,k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_415])).

cnf(c_3125,plain,
    ( k2_relat_1(X0) != k2_relat_1(sK3)
    | v1_funct_2(X0,k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2853,c_1904])).

cnf(c_4088,plain,
    ( k2_relat_1(X0) != k2_relat_1(sK3)
    | v1_funct_2(X0,k1_relat_1(X0),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3125,c_2861])).

cnf(c_4096,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4088])).

cnf(c_4859,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4096,c_33,c_35,c_2162])).

cnf(c_4863,plain,
    ( v1_funct_2(sK3,sK1,k1_relat_1(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4859,c_4585])).

cnf(c_5341,plain,
    ( r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,sK1) != iProver_top
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4880,c_33,c_4863])).

cnf(c_5342,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5341])).

cnf(c_6,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_16,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_308,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_6,c_16])).

cnf(c_312,plain,
    ( ~ v1_funct_1(X0)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_308,c_5])).

cnf(c_313,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(renaming,[status(thm)],[c_312])).

cnf(c_1906,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_2714,plain,
    ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1912,c_1906])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_36,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3352,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2714,c_36])).

cnf(c_3353,plain,
    ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3352])).

cnf(c_5350,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | k1_relat_1(sK4) = k1_xboole_0
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5342,c_3353])).

cnf(c_5459,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3864,c_5350])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_378,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X2)
    | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
    | k1_relset_1(X2,X5,X4) != k1_relset_1(sK2,sK0,sK4)
    | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_1905,plain,
    ( k2_relset_1(X0,X1,X2) != k2_relset_1(sK1,sK2,sK3)
    | k1_relset_1(X1,X3,X4) != k1_relset_1(sK2,sK0,sK4)
    | k1_funct_1(k8_funct_2(X0,X1,X3,X2,X4),X5) = k1_funct_1(X4,k1_funct_1(X2,X5))
    | k1_xboole_0 = X0
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_2482,plain,
    ( k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1905])).

cnf(c_32,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_91,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1449,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2195,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1449])).

cnf(c_2196,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2195])).

cnf(c_2487,plain,
    ( m1_subset_1(X2,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2482,c_32,c_33,c_34,c_35,c_23,c_91,c_0,c_2196])).

cnf(c_2488,plain,
    ( k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2487])).

cnf(c_2498,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2488])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2553,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2498,c_36,c_37])).

cnf(c_2561,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1913,c_2553])).

cnf(c_22,negated_conjecture,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2563,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_2561,c_22])).

cnf(c_5460,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5459,c_2563])).

cnf(c_5467,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5460,c_4871])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1919,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5842,plain,
    ( sK1 = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5467,c_1919])).

cnf(c_93,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2361,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2364,plain,
    ( k1_xboole_0 = sK3
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2361])).

cnf(c_1448,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2427,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1448])).

cnf(c_2868,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1449])).

cnf(c_3761,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2868])).

cnf(c_3762,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_3761])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1923,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4878,plain,
    ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4871,c_1923])).

cnf(c_5465,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5460,c_4878])).

cnf(c_5927,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5842,c_93,c_2364,c_2427,c_3762,c_5465])).

cnf(c_5938,plain,
    ( k1_relat_1(k1_xboole_0) = sK1 ),
    inference(demodulation,[status(thm)],[c_5927,c_4585])).

cnf(c_4,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_5977,plain,
    ( sK1 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5938,c_4])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5977,c_2196,c_0,c_91,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:30:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.92/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/0.98  
% 2.92/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.92/0.98  
% 2.92/0.98  ------  iProver source info
% 2.92/0.98  
% 2.92/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.92/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.92/0.98  git: non_committed_changes: false
% 2.92/0.98  git: last_make_outside_of_git: false
% 2.92/0.98  
% 2.92/0.98  ------ 
% 2.92/0.98  
% 2.92/0.98  ------ Input Options
% 2.92/0.98  
% 2.92/0.98  --out_options                           all
% 2.92/0.98  --tptp_safe_out                         true
% 2.92/0.98  --problem_path                          ""
% 2.92/0.98  --include_path                          ""
% 2.92/0.98  --clausifier                            res/vclausify_rel
% 2.92/0.98  --clausifier_options                    --mode clausify
% 2.92/0.98  --stdin                                 false
% 2.92/0.98  --stats_out                             all
% 2.92/0.98  
% 2.92/0.98  ------ General Options
% 2.92/0.98  
% 2.92/0.98  --fof                                   false
% 2.92/0.98  --time_out_real                         305.
% 2.92/0.98  --time_out_virtual                      -1.
% 2.92/0.98  --symbol_type_check                     false
% 2.92/0.98  --clausify_out                          false
% 2.92/0.98  --sig_cnt_out                           false
% 2.92/0.99  --trig_cnt_out                          false
% 2.92/0.99  --trig_cnt_out_tolerance                1.
% 2.92/0.99  --trig_cnt_out_sk_spl                   false
% 2.92/0.99  --abstr_cl_out                          false
% 2.92/0.99  
% 2.92/0.99  ------ Global Options
% 2.92/0.99  
% 2.92/0.99  --schedule                              default
% 2.92/0.99  --add_important_lit                     false
% 2.92/0.99  --prop_solver_per_cl                    1000
% 2.92/0.99  --min_unsat_core                        false
% 2.92/0.99  --soft_assumptions                      false
% 2.92/0.99  --soft_lemma_size                       3
% 2.92/0.99  --prop_impl_unit_size                   0
% 2.92/0.99  --prop_impl_unit                        []
% 2.92/0.99  --share_sel_clauses                     true
% 2.92/0.99  --reset_solvers                         false
% 2.92/0.99  --bc_imp_inh                            [conj_cone]
% 2.92/0.99  --conj_cone_tolerance                   3.
% 2.92/0.99  --extra_neg_conj                        none
% 2.92/0.99  --large_theory_mode                     true
% 2.92/0.99  --prolific_symb_bound                   200
% 2.92/0.99  --lt_threshold                          2000
% 2.92/0.99  --clause_weak_htbl                      true
% 2.92/0.99  --gc_record_bc_elim                     false
% 2.92/0.99  
% 2.92/0.99  ------ Preprocessing Options
% 2.92/0.99  
% 2.92/0.99  --preprocessing_flag                    true
% 2.92/0.99  --time_out_prep_mult                    0.1
% 2.92/0.99  --splitting_mode                        input
% 2.92/0.99  --splitting_grd                         true
% 2.92/0.99  --splitting_cvd                         false
% 2.92/0.99  --splitting_cvd_svl                     false
% 2.92/0.99  --splitting_nvd                         32
% 2.92/0.99  --sub_typing                            true
% 2.92/0.99  --prep_gs_sim                           true
% 2.92/0.99  --prep_unflatten                        true
% 2.92/0.99  --prep_res_sim                          true
% 2.92/0.99  --prep_upred                            true
% 2.92/0.99  --prep_sem_filter                       exhaustive
% 2.92/0.99  --prep_sem_filter_out                   false
% 2.92/0.99  --pred_elim                             true
% 2.92/0.99  --res_sim_input                         true
% 2.92/0.99  --eq_ax_congr_red                       true
% 2.92/0.99  --pure_diseq_elim                       true
% 2.92/0.99  --brand_transform                       false
% 2.92/0.99  --non_eq_to_eq                          false
% 2.92/0.99  --prep_def_merge                        true
% 2.92/0.99  --prep_def_merge_prop_impl              false
% 2.92/0.99  --prep_def_merge_mbd                    true
% 2.92/0.99  --prep_def_merge_tr_red                 false
% 2.92/0.99  --prep_def_merge_tr_cl                  false
% 2.92/0.99  --smt_preprocessing                     true
% 2.92/0.99  --smt_ac_axioms                         fast
% 2.92/0.99  --preprocessed_out                      false
% 2.92/0.99  --preprocessed_stats                    false
% 2.92/0.99  
% 2.92/0.99  ------ Abstraction refinement Options
% 2.92/0.99  
% 2.92/0.99  --abstr_ref                             []
% 2.92/0.99  --abstr_ref_prep                        false
% 2.92/0.99  --abstr_ref_until_sat                   false
% 2.92/0.99  --abstr_ref_sig_restrict                funpre
% 2.92/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.92/0.99  --abstr_ref_under                       []
% 2.92/0.99  
% 2.92/0.99  ------ SAT Options
% 2.92/0.99  
% 2.92/0.99  --sat_mode                              false
% 2.92/0.99  --sat_fm_restart_options                ""
% 2.92/0.99  --sat_gr_def                            false
% 2.92/0.99  --sat_epr_types                         true
% 2.92/0.99  --sat_non_cyclic_types                  false
% 2.92/0.99  --sat_finite_models                     false
% 2.92/0.99  --sat_fm_lemmas                         false
% 2.92/0.99  --sat_fm_prep                           false
% 2.92/0.99  --sat_fm_uc_incr                        true
% 2.92/0.99  --sat_out_model                         small
% 2.92/0.99  --sat_out_clauses                       false
% 2.92/0.99  
% 2.92/0.99  ------ QBF Options
% 2.92/0.99  
% 2.92/0.99  --qbf_mode                              false
% 2.92/0.99  --qbf_elim_univ                         false
% 2.92/0.99  --qbf_dom_inst                          none
% 2.92/0.99  --qbf_dom_pre_inst                      false
% 2.92/0.99  --qbf_sk_in                             false
% 2.92/0.99  --qbf_pred_elim                         true
% 2.92/0.99  --qbf_split                             512
% 2.92/0.99  
% 2.92/0.99  ------ BMC1 Options
% 2.92/0.99  
% 2.92/0.99  --bmc1_incremental                      false
% 2.92/0.99  --bmc1_axioms                           reachable_all
% 2.92/0.99  --bmc1_min_bound                        0
% 2.92/0.99  --bmc1_max_bound                        -1
% 2.92/0.99  --bmc1_max_bound_default                -1
% 2.92/0.99  --bmc1_symbol_reachability              true
% 2.92/0.99  --bmc1_property_lemmas                  false
% 2.92/0.99  --bmc1_k_induction                      false
% 2.92/0.99  --bmc1_non_equiv_states                 false
% 2.92/0.99  --bmc1_deadlock                         false
% 2.92/0.99  --bmc1_ucm                              false
% 2.92/0.99  --bmc1_add_unsat_core                   none
% 2.92/0.99  --bmc1_unsat_core_children              false
% 2.92/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.92/0.99  --bmc1_out_stat                         full
% 2.92/0.99  --bmc1_ground_init                      false
% 2.92/0.99  --bmc1_pre_inst_next_state              false
% 2.92/0.99  --bmc1_pre_inst_state                   false
% 2.92/0.99  --bmc1_pre_inst_reach_state             false
% 2.92/0.99  --bmc1_out_unsat_core                   false
% 2.92/0.99  --bmc1_aig_witness_out                  false
% 2.92/0.99  --bmc1_verbose                          false
% 2.92/0.99  --bmc1_dump_clauses_tptp                false
% 2.92/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.92/0.99  --bmc1_dump_file                        -
% 2.92/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.92/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.92/0.99  --bmc1_ucm_extend_mode                  1
% 2.92/0.99  --bmc1_ucm_init_mode                    2
% 2.92/0.99  --bmc1_ucm_cone_mode                    none
% 2.92/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.92/0.99  --bmc1_ucm_relax_model                  4
% 2.92/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.92/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.92/0.99  --bmc1_ucm_layered_model                none
% 2.92/0.99  --bmc1_ucm_max_lemma_size               10
% 2.92/0.99  
% 2.92/0.99  ------ AIG Options
% 2.92/0.99  
% 2.92/0.99  --aig_mode                              false
% 2.92/0.99  
% 2.92/0.99  ------ Instantiation Options
% 2.92/0.99  
% 2.92/0.99  --instantiation_flag                    true
% 2.92/0.99  --inst_sos_flag                         false
% 2.92/0.99  --inst_sos_phase                        true
% 2.92/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.92/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.92/0.99  --inst_lit_sel_side                     num_symb
% 2.92/0.99  --inst_solver_per_active                1400
% 2.92/0.99  --inst_solver_calls_frac                1.
% 2.92/0.99  --inst_passive_queue_type               priority_queues
% 2.92/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.92/0.99  --inst_passive_queues_freq              [25;2]
% 2.92/0.99  --inst_dismatching                      true
% 2.92/0.99  --inst_eager_unprocessed_to_passive     true
% 2.92/0.99  --inst_prop_sim_given                   true
% 2.92/0.99  --inst_prop_sim_new                     false
% 2.92/0.99  --inst_subs_new                         false
% 2.92/0.99  --inst_eq_res_simp                      false
% 2.92/0.99  --inst_subs_given                       false
% 2.92/0.99  --inst_orphan_elimination               true
% 2.92/0.99  --inst_learning_loop_flag               true
% 2.92/0.99  --inst_learning_start                   3000
% 2.92/0.99  --inst_learning_factor                  2
% 2.92/0.99  --inst_start_prop_sim_after_learn       3
% 2.92/0.99  --inst_sel_renew                        solver
% 2.92/0.99  --inst_lit_activity_flag                true
% 2.92/0.99  --inst_restr_to_given                   false
% 2.92/0.99  --inst_activity_threshold               500
% 2.92/0.99  --inst_out_proof                        true
% 2.92/0.99  
% 2.92/0.99  ------ Resolution Options
% 2.92/0.99  
% 2.92/0.99  --resolution_flag                       true
% 2.92/0.99  --res_lit_sel                           adaptive
% 2.92/0.99  --res_lit_sel_side                      none
% 2.92/0.99  --res_ordering                          kbo
% 2.92/0.99  --res_to_prop_solver                    active
% 2.92/0.99  --res_prop_simpl_new                    false
% 2.92/0.99  --res_prop_simpl_given                  true
% 2.92/0.99  --res_passive_queue_type                priority_queues
% 2.92/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.92/0.99  --res_passive_queues_freq               [15;5]
% 2.92/0.99  --res_forward_subs                      full
% 2.92/0.99  --res_backward_subs                     full
% 2.92/0.99  --res_forward_subs_resolution           true
% 2.92/0.99  --res_backward_subs_resolution          true
% 2.92/0.99  --res_orphan_elimination                true
% 2.92/0.99  --res_time_limit                        2.
% 2.92/0.99  --res_out_proof                         true
% 2.92/0.99  
% 2.92/0.99  ------ Superposition Options
% 2.92/0.99  
% 2.92/0.99  --superposition_flag                    true
% 2.92/0.99  --sup_passive_queue_type                priority_queues
% 2.92/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.92/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.92/0.99  --demod_completeness_check              fast
% 2.92/0.99  --demod_use_ground                      true
% 2.92/0.99  --sup_to_prop_solver                    passive
% 2.92/0.99  --sup_prop_simpl_new                    true
% 2.92/0.99  --sup_prop_simpl_given                  true
% 2.92/0.99  --sup_fun_splitting                     false
% 2.92/0.99  --sup_smt_interval                      50000
% 2.92/0.99  
% 2.92/0.99  ------ Superposition Simplification Setup
% 2.92/0.99  
% 2.92/0.99  --sup_indices_passive                   []
% 2.92/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.92/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.99  --sup_full_bw                           [BwDemod]
% 2.92/0.99  --sup_immed_triv                        [TrivRules]
% 2.92/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.92/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.99  --sup_immed_bw_main                     []
% 2.92/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.92/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.99  
% 2.92/0.99  ------ Combination Options
% 2.92/0.99  
% 2.92/0.99  --comb_res_mult                         3
% 2.92/0.99  --comb_sup_mult                         2
% 2.92/0.99  --comb_inst_mult                        10
% 2.92/0.99  
% 2.92/0.99  ------ Debug Options
% 2.92/0.99  
% 2.92/0.99  --dbg_backtrace                         false
% 2.92/0.99  --dbg_dump_prop_clauses                 false
% 2.92/0.99  --dbg_dump_prop_clauses_file            -
% 2.92/0.99  --dbg_out_stat                          false
% 2.92/0.99  ------ Parsing...
% 2.92/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.92/0.99  
% 2.92/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.92/0.99  
% 2.92/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.92/0.99  
% 2.92/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.92/0.99  ------ Proving...
% 2.92/0.99  ------ Problem Properties 
% 2.92/0.99  
% 2.92/0.99  
% 2.92/0.99  clauses                                 29
% 2.92/0.99  conjectures                             9
% 2.92/0.99  EPR                                     9
% 2.92/0.99  Horn                                    22
% 2.92/0.99  unary                                   12
% 2.92/0.99  binary                                  4
% 2.92/0.99  lits                                    76
% 2.92/0.99  lits eq                                 24
% 2.92/0.99  fd_pure                                 0
% 2.92/0.99  fd_pseudo                               0
% 2.92/0.99  fd_cond                                 6
% 2.92/0.99  fd_pseudo_cond                          0
% 2.92/0.99  AC symbols                              0
% 2.92/0.99  
% 2.92/0.99  ------ Schedule dynamic 5 is on 
% 2.92/0.99  
% 2.92/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.92/0.99  
% 2.92/0.99  
% 2.92/0.99  ------ 
% 2.92/0.99  Current options:
% 2.92/0.99  ------ 
% 2.92/0.99  
% 2.92/0.99  ------ Input Options
% 2.92/0.99  
% 2.92/0.99  --out_options                           all
% 2.92/0.99  --tptp_safe_out                         true
% 2.92/0.99  --problem_path                          ""
% 2.92/0.99  --include_path                          ""
% 2.92/0.99  --clausifier                            res/vclausify_rel
% 2.92/0.99  --clausifier_options                    --mode clausify
% 2.92/0.99  --stdin                                 false
% 2.92/0.99  --stats_out                             all
% 2.92/0.99  
% 2.92/0.99  ------ General Options
% 2.92/0.99  
% 2.92/0.99  --fof                                   false
% 2.92/0.99  --time_out_real                         305.
% 2.92/0.99  --time_out_virtual                      -1.
% 2.92/0.99  --symbol_type_check                     false
% 2.92/0.99  --clausify_out                          false
% 2.92/0.99  --sig_cnt_out                           false
% 2.92/0.99  --trig_cnt_out                          false
% 2.92/0.99  --trig_cnt_out_tolerance                1.
% 2.92/0.99  --trig_cnt_out_sk_spl                   false
% 2.92/0.99  --abstr_cl_out                          false
% 2.92/0.99  
% 2.92/0.99  ------ Global Options
% 2.92/0.99  
% 2.92/0.99  --schedule                              default
% 2.92/0.99  --add_important_lit                     false
% 2.92/0.99  --prop_solver_per_cl                    1000
% 2.92/0.99  --min_unsat_core                        false
% 2.92/0.99  --soft_assumptions                      false
% 2.92/0.99  --soft_lemma_size                       3
% 2.92/0.99  --prop_impl_unit_size                   0
% 2.92/0.99  --prop_impl_unit                        []
% 2.92/0.99  --share_sel_clauses                     true
% 2.92/0.99  --reset_solvers                         false
% 2.92/0.99  --bc_imp_inh                            [conj_cone]
% 2.92/0.99  --conj_cone_tolerance                   3.
% 2.92/0.99  --extra_neg_conj                        none
% 2.92/0.99  --large_theory_mode                     true
% 2.92/0.99  --prolific_symb_bound                   200
% 2.92/0.99  --lt_threshold                          2000
% 2.92/0.99  --clause_weak_htbl                      true
% 2.92/0.99  --gc_record_bc_elim                     false
% 2.92/0.99  
% 2.92/0.99  ------ Preprocessing Options
% 2.92/0.99  
% 2.92/0.99  --preprocessing_flag                    true
% 2.92/0.99  --time_out_prep_mult                    0.1
% 2.92/0.99  --splitting_mode                        input
% 2.92/0.99  --splitting_grd                         true
% 2.92/0.99  --splitting_cvd                         false
% 2.92/0.99  --splitting_cvd_svl                     false
% 2.92/0.99  --splitting_nvd                         32
% 2.92/0.99  --sub_typing                            true
% 2.92/0.99  --prep_gs_sim                           true
% 2.92/0.99  --prep_unflatten                        true
% 2.92/0.99  --prep_res_sim                          true
% 2.92/0.99  --prep_upred                            true
% 2.92/0.99  --prep_sem_filter                       exhaustive
% 2.92/0.99  --prep_sem_filter_out                   false
% 2.92/0.99  --pred_elim                             true
% 2.92/0.99  --res_sim_input                         true
% 2.92/0.99  --eq_ax_congr_red                       true
% 2.92/0.99  --pure_diseq_elim                       true
% 2.92/0.99  --brand_transform                       false
% 2.92/0.99  --non_eq_to_eq                          false
% 2.92/0.99  --prep_def_merge                        true
% 2.92/0.99  --prep_def_merge_prop_impl              false
% 2.92/0.99  --prep_def_merge_mbd                    true
% 2.92/0.99  --prep_def_merge_tr_red                 false
% 2.92/0.99  --prep_def_merge_tr_cl                  false
% 2.92/0.99  --smt_preprocessing                     true
% 2.92/0.99  --smt_ac_axioms                         fast
% 2.92/0.99  --preprocessed_out                      false
% 2.92/0.99  --preprocessed_stats                    false
% 2.92/0.99  
% 2.92/0.99  ------ Abstraction refinement Options
% 2.92/0.99  
% 2.92/0.99  --abstr_ref                             []
% 2.92/0.99  --abstr_ref_prep                        false
% 2.92/0.99  --abstr_ref_until_sat                   false
% 2.92/0.99  --abstr_ref_sig_restrict                funpre
% 2.92/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.92/0.99  --abstr_ref_under                       []
% 2.92/0.99  
% 2.92/0.99  ------ SAT Options
% 2.92/0.99  
% 2.92/0.99  --sat_mode                              false
% 2.92/0.99  --sat_fm_restart_options                ""
% 2.92/0.99  --sat_gr_def                            false
% 2.92/0.99  --sat_epr_types                         true
% 2.92/0.99  --sat_non_cyclic_types                  false
% 2.92/0.99  --sat_finite_models                     false
% 2.92/0.99  --sat_fm_lemmas                         false
% 2.92/0.99  --sat_fm_prep                           false
% 2.92/0.99  --sat_fm_uc_incr                        true
% 2.92/0.99  --sat_out_model                         small
% 2.92/0.99  --sat_out_clauses                       false
% 2.92/0.99  
% 2.92/0.99  ------ QBF Options
% 2.92/0.99  
% 2.92/0.99  --qbf_mode                              false
% 2.92/0.99  --qbf_elim_univ                         false
% 2.92/0.99  --qbf_dom_inst                          none
% 2.92/0.99  --qbf_dom_pre_inst                      false
% 2.92/0.99  --qbf_sk_in                             false
% 2.92/0.99  --qbf_pred_elim                         true
% 2.92/0.99  --qbf_split                             512
% 2.92/0.99  
% 2.92/0.99  ------ BMC1 Options
% 2.92/0.99  
% 2.92/0.99  --bmc1_incremental                      false
% 2.92/0.99  --bmc1_axioms                           reachable_all
% 2.92/0.99  --bmc1_min_bound                        0
% 2.92/0.99  --bmc1_max_bound                        -1
% 2.92/0.99  --bmc1_max_bound_default                -1
% 2.92/0.99  --bmc1_symbol_reachability              true
% 2.92/0.99  --bmc1_property_lemmas                  false
% 2.92/0.99  --bmc1_k_induction                      false
% 2.92/0.99  --bmc1_non_equiv_states                 false
% 2.92/0.99  --bmc1_deadlock                         false
% 2.92/0.99  --bmc1_ucm                              false
% 2.92/0.99  --bmc1_add_unsat_core                   none
% 2.92/0.99  --bmc1_unsat_core_children              false
% 2.92/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.92/0.99  --bmc1_out_stat                         full
% 2.92/0.99  --bmc1_ground_init                      false
% 2.92/0.99  --bmc1_pre_inst_next_state              false
% 2.92/0.99  --bmc1_pre_inst_state                   false
% 2.92/0.99  --bmc1_pre_inst_reach_state             false
% 2.92/0.99  --bmc1_out_unsat_core                   false
% 2.92/0.99  --bmc1_aig_witness_out                  false
% 2.92/0.99  --bmc1_verbose                          false
% 2.92/0.99  --bmc1_dump_clauses_tptp                false
% 2.92/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.92/0.99  --bmc1_dump_file                        -
% 2.92/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.92/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.92/0.99  --bmc1_ucm_extend_mode                  1
% 2.92/0.99  --bmc1_ucm_init_mode                    2
% 2.92/0.99  --bmc1_ucm_cone_mode                    none
% 2.92/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.92/0.99  --bmc1_ucm_relax_model                  4
% 2.92/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.92/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.92/0.99  --bmc1_ucm_layered_model                none
% 2.92/0.99  --bmc1_ucm_max_lemma_size               10
% 2.92/0.99  
% 2.92/0.99  ------ AIG Options
% 2.92/0.99  
% 2.92/0.99  --aig_mode                              false
% 2.92/0.99  
% 2.92/0.99  ------ Instantiation Options
% 2.92/0.99  
% 2.92/0.99  --instantiation_flag                    true
% 2.92/0.99  --inst_sos_flag                         false
% 2.92/0.99  --inst_sos_phase                        true
% 2.92/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.92/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.92/0.99  --inst_lit_sel_side                     none
% 2.92/0.99  --inst_solver_per_active                1400
% 2.92/0.99  --inst_solver_calls_frac                1.
% 2.92/0.99  --inst_passive_queue_type               priority_queues
% 2.92/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.92/0.99  --inst_passive_queues_freq              [25;2]
% 2.92/0.99  --inst_dismatching                      true
% 2.92/0.99  --inst_eager_unprocessed_to_passive     true
% 2.92/0.99  --inst_prop_sim_given                   true
% 2.92/0.99  --inst_prop_sim_new                     false
% 2.92/0.99  --inst_subs_new                         false
% 2.92/0.99  --inst_eq_res_simp                      false
% 2.92/0.99  --inst_subs_given                       false
% 2.92/0.99  --inst_orphan_elimination               true
% 2.92/0.99  --inst_learning_loop_flag               true
% 2.92/0.99  --inst_learning_start                   3000
% 2.92/0.99  --inst_learning_factor                  2
% 2.92/0.99  --inst_start_prop_sim_after_learn       3
% 2.92/0.99  --inst_sel_renew                        solver
% 2.92/0.99  --inst_lit_activity_flag                true
% 2.92/0.99  --inst_restr_to_given                   false
% 2.92/0.99  --inst_activity_threshold               500
% 2.92/0.99  --inst_out_proof                        true
% 2.92/0.99  
% 2.92/0.99  ------ Resolution Options
% 2.92/0.99  
% 2.92/0.99  --resolution_flag                       false
% 2.92/0.99  --res_lit_sel                           adaptive
% 2.92/0.99  --res_lit_sel_side                      none
% 2.92/0.99  --res_ordering                          kbo
% 2.92/0.99  --res_to_prop_solver                    active
% 2.92/0.99  --res_prop_simpl_new                    false
% 2.92/0.99  --res_prop_simpl_given                  true
% 2.92/0.99  --res_passive_queue_type                priority_queues
% 2.92/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.92/0.99  --res_passive_queues_freq               [15;5]
% 2.92/0.99  --res_forward_subs                      full
% 2.92/0.99  --res_backward_subs                     full
% 2.92/0.99  --res_forward_subs_resolution           true
% 2.92/0.99  --res_backward_subs_resolution          true
% 2.92/0.99  --res_orphan_elimination                true
% 2.92/0.99  --res_time_limit                        2.
% 2.92/0.99  --res_out_proof                         true
% 2.92/0.99  
% 2.92/0.99  ------ Superposition Options
% 2.92/0.99  
% 2.92/0.99  --superposition_flag                    true
% 2.92/0.99  --sup_passive_queue_type                priority_queues
% 2.92/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.92/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.92/0.99  --demod_completeness_check              fast
% 2.92/0.99  --demod_use_ground                      true
% 2.92/0.99  --sup_to_prop_solver                    passive
% 2.92/0.99  --sup_prop_simpl_new                    true
% 2.92/0.99  --sup_prop_simpl_given                  true
% 2.92/0.99  --sup_fun_splitting                     false
% 2.92/0.99  --sup_smt_interval                      50000
% 2.92/0.99  
% 2.92/0.99  ------ Superposition Simplification Setup
% 2.92/0.99  
% 2.92/0.99  --sup_indices_passive                   []
% 2.92/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.92/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.99  --sup_full_bw                           [BwDemod]
% 2.92/0.99  --sup_immed_triv                        [TrivRules]
% 2.92/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.92/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.99  --sup_immed_bw_main                     []
% 2.92/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.92/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.99  
% 2.92/0.99  ------ Combination Options
% 2.92/0.99  
% 2.92/0.99  --comb_res_mult                         3
% 2.92/0.99  --comb_sup_mult                         2
% 2.92/0.99  --comb_inst_mult                        10
% 2.92/0.99  
% 2.92/0.99  ------ Debug Options
% 2.92/0.99  
% 2.92/0.99  --dbg_backtrace                         false
% 2.92/0.99  --dbg_dump_prop_clauses                 false
% 2.92/0.99  --dbg_dump_prop_clauses_file            -
% 2.92/0.99  --dbg_out_stat                          false
% 2.92/0.99  
% 2.92/0.99  
% 2.92/0.99  
% 2.92/0.99  
% 2.92/0.99  ------ Proving...
% 2.92/0.99  
% 2.92/0.99  
% 2.92/0.99  % SZS status Theorem for theBenchmark.p
% 2.92/0.99  
% 2.92/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.92/0.99  
% 2.92/0.99  fof(f15,conjecture,(
% 2.92/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.99  
% 2.92/0.99  fof(f16,negated_conjecture,(
% 2.92/0.99    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.92/0.99    inference(negated_conjecture,[],[f15])).
% 2.92/0.99  
% 2.92/0.99  fof(f36,plain,(
% 2.92/0.99    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 2.92/0.99    inference(ennf_transformation,[],[f16])).
% 2.92/0.99  
% 2.92/0.99  fof(f37,plain,(
% 2.92/0.99    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 2.92/0.99    inference(flattening,[],[f36])).
% 2.92/0.99  
% 2.92/0.99  fof(f42,plain,(
% 2.92/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k7_partfun1(X0,X4,k1_funct_1(X3,sK5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK5,X1))) )),
% 2.92/0.99    introduced(choice_axiom,[])).
% 2.92/0.99  
% 2.92/0.99  fof(f41,plain,(
% 2.92/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k7_partfun1(X0,sK4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4)) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK4))) )),
% 2.92/0.99    introduced(choice_axiom,[])).
% 2.92/0.99  
% 2.92/0.99  fof(f40,plain,(
% 2.92/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(sK3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK3,X1,X2) & v1_funct_1(sK3))) )),
% 2.92/0.99    introduced(choice_axiom,[])).
% 2.92/0.99  
% 2.92/0.99  fof(f39,plain,(
% 2.92/0.99    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 2.92/0.99    introduced(choice_axiom,[])).
% 2.92/0.99  
% 2.92/0.99  fof(f43,plain,(
% 2.92/0.99    (((k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 2.92/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f37,f42,f41,f40,f39])).
% 2.92/0.99  
% 2.92/0.99  fof(f72,plain,(
% 2.92/0.99    m1_subset_1(sK5,sK1)),
% 2.92/0.99    inference(cnf_transformation,[],[f43])).
% 2.92/0.99  
% 2.92/0.99  fof(f3,axiom,(
% 2.92/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.99  
% 2.92/0.99  fof(f19,plain,(
% 2.92/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.92/0.99    inference(ennf_transformation,[],[f3])).
% 2.92/0.99  
% 2.92/0.99  fof(f20,plain,(
% 2.92/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.92/0.99    inference(flattening,[],[f19])).
% 2.92/0.99  
% 2.92/0.99  fof(f46,plain,(
% 2.92/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.92/0.99    inference(cnf_transformation,[],[f20])).
% 2.92/0.99  
% 2.92/0.99  fof(f74,plain,(
% 2.92/0.99    k1_xboole_0 != sK1),
% 2.92/0.99    inference(cnf_transformation,[],[f43])).
% 2.92/0.99  
% 2.92/0.99  fof(f2,axiom,(
% 2.92/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.99  
% 2.92/0.99  fof(f18,plain,(
% 2.92/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.92/0.99    inference(ennf_transformation,[],[f2])).
% 2.92/0.99  
% 2.92/0.99  fof(f45,plain,(
% 2.92/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.92/0.99    inference(cnf_transformation,[],[f18])).
% 2.92/0.99  
% 2.92/0.99  fof(f69,plain,(
% 2.92/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.92/0.99    inference(cnf_transformation,[],[f43])).
% 2.92/0.99  
% 2.92/0.99  fof(f9,axiom,(
% 2.92/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.99  
% 2.92/0.99  fof(f25,plain,(
% 2.92/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/0.99    inference(ennf_transformation,[],[f9])).
% 2.92/0.99  
% 2.92/0.99  fof(f53,plain,(
% 2.92/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/0.99    inference(cnf_transformation,[],[f25])).
% 2.92/0.99  
% 2.92/0.99  fof(f13,axiom,(
% 2.92/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.99  
% 2.92/0.99  fof(f32,plain,(
% 2.92/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.92/0.99    inference(ennf_transformation,[],[f13])).
% 2.92/0.99  
% 2.92/0.99  fof(f33,plain,(
% 2.92/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.92/0.99    inference(flattening,[],[f32])).
% 2.92/0.99  
% 2.92/0.99  fof(f64,plain,(
% 2.92/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.92/0.99    inference(cnf_transformation,[],[f33])).
% 2.92/0.99  
% 2.92/0.99  fof(f73,plain,(
% 2.92/0.99    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 2.92/0.99    inference(cnf_transformation,[],[f43])).
% 2.92/0.99  
% 2.92/0.99  fof(f71,plain,(
% 2.92/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 2.92/0.99    inference(cnf_transformation,[],[f43])).
% 2.92/0.99  
% 2.92/0.99  fof(f8,axiom,(
% 2.92/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.99  
% 2.92/0.99  fof(f24,plain,(
% 2.92/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/0.99    inference(ennf_transformation,[],[f8])).
% 2.92/0.99  
% 2.92/0.99  fof(f52,plain,(
% 2.92/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/0.99    inference(cnf_transformation,[],[f24])).
% 2.92/0.99  
% 2.92/0.99  fof(f67,plain,(
% 2.92/0.99    v1_funct_1(sK3)),
% 2.92/0.99    inference(cnf_transformation,[],[f43])).
% 2.92/0.99  
% 2.92/0.99  fof(f5,axiom,(
% 2.92/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.99  
% 2.92/0.99  fof(f21,plain,(
% 2.92/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/0.99    inference(ennf_transformation,[],[f5])).
% 2.92/0.99  
% 2.92/0.99  fof(f49,plain,(
% 2.92/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/0.99    inference(cnf_transformation,[],[f21])).
% 2.92/0.99  
% 2.92/0.99  fof(f10,axiom,(
% 2.92/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.99  
% 2.92/0.99  fof(f26,plain,(
% 2.92/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/0.99    inference(ennf_transformation,[],[f10])).
% 2.92/0.99  
% 2.92/0.99  fof(f27,plain,(
% 2.92/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/0.99    inference(flattening,[],[f26])).
% 2.92/0.99  
% 2.92/0.99  fof(f38,plain,(
% 2.92/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/0.99    inference(nnf_transformation,[],[f27])).
% 2.92/0.99  
% 2.92/0.99  fof(f54,plain,(
% 2.92/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/0.99    inference(cnf_transformation,[],[f38])).
% 2.92/0.99  
% 2.92/0.99  fof(f66,plain,(
% 2.92/0.99    ~v1_xboole_0(sK2)),
% 2.92/0.99    inference(cnf_transformation,[],[f43])).
% 2.92/0.99  
% 2.92/0.99  fof(f68,plain,(
% 2.92/0.99    v1_funct_2(sK3,sK1,sK2)),
% 2.92/0.99    inference(cnf_transformation,[],[f43])).
% 2.92/0.99  
% 2.92/0.99  fof(f1,axiom,(
% 2.92/0.99    v1_xboole_0(k1_xboole_0)),
% 2.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.99  
% 2.92/0.99  fof(f44,plain,(
% 2.92/0.99    v1_xboole_0(k1_xboole_0)),
% 2.92/0.99    inference(cnf_transformation,[],[f1])).
% 2.92/0.99  
% 2.92/0.99  fof(f14,axiom,(
% 2.92/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.99  
% 2.92/0.99  fof(f34,plain,(
% 2.92/0.99    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.92/0.99    inference(ennf_transformation,[],[f14])).
% 2.92/0.99  
% 2.92/0.99  fof(f35,plain,(
% 2.92/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.92/0.99    inference(flattening,[],[f34])).
% 2.92/0.99  
% 2.92/0.99  fof(f65,plain,(
% 2.92/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.92/0.99    inference(cnf_transformation,[],[f35])).
% 2.92/0.99  
% 2.92/0.99  fof(f63,plain,(
% 2.92/0.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.92/0.99    inference(cnf_transformation,[],[f33])).
% 2.92/0.99  
% 2.92/0.99  fof(f6,axiom,(
% 2.92/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.99  
% 2.92/0.99  fof(f17,plain,(
% 2.92/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.92/0.99    inference(pure_predicate_removal,[],[f6])).
% 2.92/0.99  
% 2.92/0.99  fof(f22,plain,(
% 2.92/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/0.99    inference(ennf_transformation,[],[f17])).
% 2.92/0.99  
% 2.92/0.99  fof(f50,plain,(
% 2.92/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/0.99    inference(cnf_transformation,[],[f22])).
% 2.92/0.99  
% 2.92/0.99  fof(f11,axiom,(
% 2.92/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 2.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.99  
% 2.92/0.99  fof(f28,plain,(
% 2.92/0.99    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.92/0.99    inference(ennf_transformation,[],[f11])).
% 2.92/0.99  
% 2.92/0.99  fof(f29,plain,(
% 2.92/0.99    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.92/0.99    inference(flattening,[],[f28])).
% 2.92/0.99  
% 2.92/0.99  fof(f60,plain,(
% 2.92/0.99    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.92/0.99    inference(cnf_transformation,[],[f29])).
% 2.92/0.99  
% 2.92/0.99  fof(f70,plain,(
% 2.92/0.99    v1_funct_1(sK4)),
% 2.92/0.99    inference(cnf_transformation,[],[f43])).
% 2.92/0.99  
% 2.92/0.99  fof(f12,axiom,(
% 2.92/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.99  
% 2.92/0.99  fof(f30,plain,(
% 2.92/0.99    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.92/0.99    inference(ennf_transformation,[],[f12])).
% 2.92/0.99  
% 2.92/0.99  fof(f31,plain,(
% 2.92/0.99    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.92/0.99    inference(flattening,[],[f30])).
% 2.92/0.99  
% 2.92/0.99  fof(f61,plain,(
% 2.92/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 2.92/0.99    inference(cnf_transformation,[],[f31])).
% 2.92/0.99  
% 2.92/0.99  fof(f75,plain,(
% 2.92/0.99    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5)),
% 2.92/0.99    inference(cnf_transformation,[],[f43])).
% 2.92/0.99  
% 2.92/0.99  fof(f58,plain,(
% 2.92/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/0.99    inference(cnf_transformation,[],[f38])).
% 2.92/0.99  
% 2.92/0.99  fof(f78,plain,(
% 2.92/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.92/0.99    inference(equality_resolution,[],[f58])).
% 2.92/0.99  
% 2.92/0.99  fof(f7,axiom,(
% 2.92/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.99  
% 2.92/0.99  fof(f23,plain,(
% 2.92/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.92/0.99    inference(ennf_transformation,[],[f7])).
% 2.92/0.99  
% 2.92/0.99  fof(f51,plain,(
% 2.92/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.92/0.99    inference(cnf_transformation,[],[f23])).
% 2.92/0.99  
% 2.92/0.99  fof(f4,axiom,(
% 2.92/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.99  
% 2.92/0.99  fof(f47,plain,(
% 2.92/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.92/0.99    inference(cnf_transformation,[],[f4])).
% 2.92/0.99  
% 2.92/0.99  cnf(c_25,negated_conjecture,
% 2.92/0.99      ( m1_subset_1(sK5,sK1) ),
% 2.92/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_1913,plain,
% 2.92/0.99      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2,plain,
% 2.92/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.92/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_1925,plain,
% 2.92/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 2.92/0.99      | r2_hidden(X0,X1) = iProver_top
% 2.92/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2957,plain,
% 2.92/0.99      ( r2_hidden(sK5,sK1) = iProver_top
% 2.92/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 2.92/0.99      inference(superposition,[status(thm)],[c_1913,c_1925]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_38,plain,
% 2.92/0.99      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_23,negated_conjecture,
% 2.92/0.99      ( k1_xboole_0 != sK1 ),
% 2.92/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_1,plain,
% 2.92/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.92/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2152,plain,
% 2.92/0.99      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 2.92/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2153,plain,
% 2.92/0.99      ( k1_xboole_0 = sK1 | v1_xboole_0(sK1) != iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_2152]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2310,plain,
% 2.92/0.99      ( ~ m1_subset_1(X0,sK1) | r2_hidden(X0,sK1) | v1_xboole_0(sK1) ),
% 2.92/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2520,plain,
% 2.92/0.99      ( ~ m1_subset_1(sK5,sK1) | r2_hidden(sK5,sK1) | v1_xboole_0(sK1) ),
% 2.92/0.99      inference(instantiation,[status(thm)],[c_2310]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2521,plain,
% 2.92/0.99      ( m1_subset_1(sK5,sK1) != iProver_top
% 2.92/0.99      | r2_hidden(sK5,sK1) = iProver_top
% 2.92/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_2520]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_3864,plain,
% 2.92/0.99      ( r2_hidden(sK5,sK1) = iProver_top ),
% 2.92/0.99      inference(global_propositional_subsumption,
% 2.92/0.99                [status(thm)],
% 2.92/0.99                [c_2957,c_38,c_23,c_2153,c_2521]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_28,negated_conjecture,
% 2.92/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.92/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_1910,plain,
% 2.92/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_9,plain,
% 2.92/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.92/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_1921,plain,
% 2.92/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.92/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2853,plain,
% 2.92/0.99      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 2.92/0.99      inference(superposition,[status(thm)],[c_1910,c_1921]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_18,plain,
% 2.92/0.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.92/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.92/0.99      | ~ v1_funct_1(X0)
% 2.92/0.99      | ~ v1_relat_1(X0) ),
% 2.92/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_24,negated_conjecture,
% 2.92/0.99      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
% 2.92/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_432,plain,
% 2.92/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.92/0.99      | ~ v1_funct_1(X0)
% 2.92/0.99      | ~ v1_relat_1(X0)
% 2.92/0.99      | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0)
% 2.92/0.99      | k1_relset_1(sK2,sK0,sK4) != X1 ),
% 2.92/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_433,plain,
% 2.92/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4))))
% 2.92/0.99      | ~ v1_funct_1(X0)
% 2.92/0.99      | ~ v1_relat_1(X0)
% 2.92/0.99      | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0) ),
% 2.92/0.99      inference(unflattening,[status(thm)],[c_432]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_1903,plain,
% 2.92/0.99      ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0)
% 2.92/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4)))) = iProver_top
% 2.92/0.99      | v1_funct_1(X0) != iProver_top
% 2.92/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_433]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_3126,plain,
% 2.92/0.99      ( k2_relat_1(X0) != k2_relat_1(sK3)
% 2.92/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4)))) = iProver_top
% 2.92/0.99      | v1_funct_1(X0) != iProver_top
% 2.92/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.92/0.99      inference(demodulation,[status(thm)],[c_2853,c_1903]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_26,negated_conjecture,
% 2.92/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 2.92/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_1912,plain,
% 2.92/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_8,plain,
% 2.92/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.92/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_1922,plain,
% 2.92/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.92/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2861,plain,
% 2.92/0.99      ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
% 2.92/0.99      inference(superposition,[status(thm)],[c_1912,c_1922]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_4099,plain,
% 2.92/0.99      ( k2_relat_1(X0) != k2_relat_1(sK3)
% 2.92/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relat_1(sK4)))) = iProver_top
% 2.92/0.99      | v1_funct_1(X0) != iProver_top
% 2.92/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.92/0.99      inference(light_normalisation,[status(thm)],[c_3126,c_2861]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_4107,plain,
% 2.92/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4)))) = iProver_top
% 2.92/0.99      | v1_funct_1(sK3) != iProver_top
% 2.92/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.92/0.99      inference(equality_resolution,[status(thm)],[c_4099]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_30,negated_conjecture,
% 2.92/0.99      ( v1_funct_1(sK3) ),
% 2.92/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_33,plain,
% 2.92/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_35,plain,
% 2.92/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_5,plain,
% 2.92/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.99      | v1_relat_1(X0) ),
% 2.92/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2161,plain,
% 2.92/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.92/0.99      | v1_relat_1(sK3) ),
% 2.92/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2162,plain,
% 2.92/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.92/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_2161]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_4867,plain,
% 2.92/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4)))) = iProver_top ),
% 2.92/0.99      inference(global_propositional_subsumption,
% 2.92/0.99                [status(thm)],
% 2.92/0.99                [c_4107,c_33,c_35,c_2162]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_15,plain,
% 2.92/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.92/0.99      | k1_xboole_0 = X2 ),
% 2.92/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_1915,plain,
% 2.92/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 2.92/0.99      | k1_xboole_0 = X1
% 2.92/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.92/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_4246,plain,
% 2.92/0.99      ( k1_relset_1(sK1,sK2,sK3) = sK1
% 2.92/0.99      | sK2 = k1_xboole_0
% 2.92/0.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
% 2.92/0.99      inference(superposition,[status(thm)],[c_1910,c_1915]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2862,plain,
% 2.92/0.99      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.92/0.99      inference(superposition,[status(thm)],[c_1910,c_1922]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_4250,plain,
% 2.92/0.99      ( k1_relat_1(sK3) = sK1
% 2.92/0.99      | sK2 = k1_xboole_0
% 2.92/0.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
% 2.92/0.99      inference(demodulation,[status(thm)],[c_4246,c_2862]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_31,negated_conjecture,
% 2.92/0.99      ( ~ v1_xboole_0(sK2) ),
% 2.92/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_29,negated_conjecture,
% 2.92/0.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.92/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_34,plain,
% 2.92/0.99      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_0,plain,
% 2.92/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.92/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_1450,plain,
% 2.92/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.92/0.99      theory(equality) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2164,plain,
% 2.92/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 != X0 ),
% 2.92/0.99      inference(instantiation,[status(thm)],[c_1450]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2166,plain,
% 2.92/0.99      ( v1_xboole_0(sK2)
% 2.92/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 2.92/0.99      | sK2 != k1_xboole_0 ),
% 2.92/0.99      inference(instantiation,[status(thm)],[c_2164]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_4585,plain,
% 2.92/0.99      ( k1_relat_1(sK3) = sK1 ),
% 2.92/0.99      inference(global_propositional_subsumption,
% 2.92/0.99                [status(thm)],
% 2.92/0.99                [c_4250,c_31,c_34,c_0,c_2166]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_4871,plain,
% 2.92/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) = iProver_top ),
% 2.92/0.99      inference(light_normalisation,[status(thm)],[c_4867,c_4585]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_21,plain,
% 2.92/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.99      | ~ r2_hidden(X3,X1)
% 2.92/0.99      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.92/0.99      | ~ v1_funct_1(X0)
% 2.92/0.99      | k1_xboole_0 = X2 ),
% 2.92/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_1914,plain,
% 2.92/0.99      ( k1_xboole_0 = X0
% 2.92/0.99      | v1_funct_2(X1,X2,X0) != iProver_top
% 2.92/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 2.92/0.99      | r2_hidden(X3,X2) != iProver_top
% 2.92/0.99      | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
% 2.92/0.99      | v1_funct_1(X1) != iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_4880,plain,
% 2.92/0.99      ( k1_relat_1(sK4) = k1_xboole_0
% 2.92/0.99      | v1_funct_2(sK3,sK1,k1_relat_1(sK4)) != iProver_top
% 2.92/0.99      | r2_hidden(X0,sK1) != iProver_top
% 2.92/0.99      | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
% 2.92/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.92/0.99      inference(superposition,[status(thm)],[c_4871,c_1914]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_19,plain,
% 2.92/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.92/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.92/0.99      | ~ v1_funct_1(X0)
% 2.92/0.99      | ~ v1_relat_1(X0) ),
% 2.92/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_414,plain,
% 2.92/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.92/0.99      | ~ v1_funct_1(X0)
% 2.92/0.99      | ~ v1_relat_1(X0)
% 2.92/0.99      | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0)
% 2.92/0.99      | k1_relset_1(sK2,sK0,sK4) != X1 ),
% 2.92/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_415,plain,
% 2.92/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4))
% 2.92/0.99      | ~ v1_funct_1(X0)
% 2.92/0.99      | ~ v1_relat_1(X0)
% 2.92/0.99      | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0) ),
% 2.92/0.99      inference(unflattening,[status(thm)],[c_414]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_1904,plain,
% 2.92/0.99      ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0)
% 2.92/0.99      | v1_funct_2(X0,k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4)) = iProver_top
% 2.92/0.99      | v1_funct_1(X0) != iProver_top
% 2.92/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_415]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_3125,plain,
% 2.92/0.99      ( k2_relat_1(X0) != k2_relat_1(sK3)
% 2.92/0.99      | v1_funct_2(X0,k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4)) = iProver_top
% 2.92/0.99      | v1_funct_1(X0) != iProver_top
% 2.92/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.92/0.99      inference(demodulation,[status(thm)],[c_2853,c_1904]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_4088,plain,
% 2.92/0.99      ( k2_relat_1(X0) != k2_relat_1(sK3)
% 2.92/0.99      | v1_funct_2(X0,k1_relat_1(X0),k1_relat_1(sK4)) = iProver_top
% 2.92/0.99      | v1_funct_1(X0) != iProver_top
% 2.92/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.92/0.99      inference(light_normalisation,[status(thm)],[c_3125,c_2861]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_4096,plain,
% 2.92/0.99      ( v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4)) = iProver_top
% 2.92/0.99      | v1_funct_1(sK3) != iProver_top
% 2.92/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.92/0.99      inference(equality_resolution,[status(thm)],[c_4088]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_4859,plain,
% 2.92/0.99      ( v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4)) = iProver_top ),
% 2.92/0.99      inference(global_propositional_subsumption,
% 2.92/0.99                [status(thm)],
% 2.92/0.99                [c_4096,c_33,c_35,c_2162]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_4863,plain,
% 2.92/0.99      ( v1_funct_2(sK3,sK1,k1_relat_1(sK4)) = iProver_top ),
% 2.92/0.99      inference(light_normalisation,[status(thm)],[c_4859,c_4585]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_5341,plain,
% 2.92/0.99      ( r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
% 2.92/0.99      | r2_hidden(X0,sK1) != iProver_top
% 2.92/0.99      | k1_relat_1(sK4) = k1_xboole_0 ),
% 2.92/0.99      inference(global_propositional_subsumption,
% 2.92/0.99                [status(thm)],
% 2.92/0.99                [c_4880,c_33,c_4863]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_5342,plain,
% 2.92/0.99      ( k1_relat_1(sK4) = k1_xboole_0
% 2.92/0.99      | r2_hidden(X0,sK1) != iProver_top
% 2.92/0.99      | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top ),
% 2.92/0.99      inference(renaming,[status(thm)],[c_5341]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_6,plain,
% 2.92/0.99      ( v5_relat_1(X0,X1)
% 2.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.92/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_16,plain,
% 2.92/0.99      ( ~ v5_relat_1(X0,X1)
% 2.92/0.99      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.92/0.99      | ~ v1_funct_1(X0)
% 2.92/0.99      | ~ v1_relat_1(X0)
% 2.92/0.99      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.92/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_308,plain,
% 2.92/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.99      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.92/0.99      | ~ v1_funct_1(X0)
% 2.92/0.99      | ~ v1_relat_1(X0)
% 2.92/0.99      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.92/0.99      inference(resolution,[status(thm)],[c_6,c_16]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_312,plain,
% 2.92/0.99      ( ~ v1_funct_1(X0)
% 2.92/0.99      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.99      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.92/0.99      inference(global_propositional_subsumption,
% 2.92/0.99                [status(thm)],
% 2.92/0.99                [c_308,c_5]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_313,plain,
% 2.92/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.99      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.92/0.99      | ~ v1_funct_1(X0)
% 2.92/0.99      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.92/0.99      inference(renaming,[status(thm)],[c_312]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_1906,plain,
% 2.92/0.99      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 2.92/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 2.92/0.99      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 2.92/0.99      | v1_funct_1(X1) != iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2714,plain,
% 2.92/0.99      ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
% 2.92/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.92/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.92/0.99      inference(superposition,[status(thm)],[c_1912,c_1906]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_27,negated_conjecture,
% 2.92/0.99      ( v1_funct_1(sK4) ),
% 2.92/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_36,plain,
% 2.92/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_3352,plain,
% 2.92/0.99      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.92/0.99      | k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0) ),
% 2.92/0.99      inference(global_propositional_subsumption,
% 2.92/0.99                [status(thm)],
% 2.92/0.99                [c_2714,c_36]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_3353,plain,
% 2.92/0.99      ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
% 2.92/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.92/0.99      inference(renaming,[status(thm)],[c_3352]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_5350,plain,
% 2.92/0.99      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.92/0.99      | k1_relat_1(sK4) = k1_xboole_0
% 2.92/0.99      | r2_hidden(X0,sK1) != iProver_top ),
% 2.92/0.99      inference(superposition,[status(thm)],[c_5342,c_3353]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_5459,plain,
% 2.92/0.99      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 2.92/0.99      | k1_relat_1(sK4) = k1_xboole_0 ),
% 2.92/0.99      inference(superposition,[status(thm)],[c_3864,c_5350]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_17,plain,
% 2.92/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.92/0.99      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 2.92/0.99      | ~ m1_subset_1(X5,X1)
% 2.92/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.99      | ~ v1_funct_1(X4)
% 2.92/0.99      | ~ v1_funct_1(X0)
% 2.92/0.99      | v1_xboole_0(X2)
% 2.92/0.99      | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k1_funct_1(X4,k1_funct_1(X0,X5))
% 2.92/0.99      | k1_xboole_0 = X1 ),
% 2.92/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_378,plain,
% 2.92/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.92/0.99      | ~ m1_subset_1(X3,X1)
% 2.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 2.92/0.99      | ~ v1_funct_1(X0)
% 2.92/0.99      | ~ v1_funct_1(X4)
% 2.92/0.99      | v1_xboole_0(X2)
% 2.92/0.99      | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
% 2.92/0.99      | k1_relset_1(X2,X5,X4) != k1_relset_1(sK2,sK0,sK4)
% 2.92/0.99      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 2.92/0.99      | k1_xboole_0 = X1 ),
% 2.92/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_1905,plain,
% 2.92/0.99      ( k2_relset_1(X0,X1,X2) != k2_relset_1(sK1,sK2,sK3)
% 2.92/0.99      | k1_relset_1(X1,X3,X4) != k1_relset_1(sK2,sK0,sK4)
% 2.92/0.99      | k1_funct_1(k8_funct_2(X0,X1,X3,X2,X4),X5) = k1_funct_1(X4,k1_funct_1(X2,X5))
% 2.92/0.99      | k1_xboole_0 = X0
% 2.92/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.92/0.99      | m1_subset_1(X5,X0) != iProver_top
% 2.92/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.92/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 2.92/0.99      | v1_funct_1(X2) != iProver_top
% 2.92/0.99      | v1_funct_1(X4) != iProver_top
% 2.92/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_378]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2482,plain,
% 2.92/0.99      ( k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
% 2.92/0.99      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.92/0.99      | sK1 = k1_xboole_0
% 2.92/0.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.92/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 2.92/0.99      | m1_subset_1(X2,sK1) != iProver_top
% 2.92/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.92/0.99      | v1_funct_1(X1) != iProver_top
% 2.92/0.99      | v1_funct_1(sK3) != iProver_top
% 2.92/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 2.92/0.99      inference(equality_resolution,[status(thm)],[c_1905]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_32,plain,
% 2.92/0.99      ( v1_xboole_0(sK2) != iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_91,plain,
% 2.92/0.99      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 2.92/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_1449,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2195,plain,
% 2.92/0.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 2.92/0.99      inference(instantiation,[status(thm)],[c_1449]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2196,plain,
% 2.92/0.99      ( sK1 != k1_xboole_0
% 2.92/0.99      | k1_xboole_0 = sK1
% 2.92/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.92/0.99      inference(instantiation,[status(thm)],[c_2195]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2487,plain,
% 2.92/0.99      ( m1_subset_1(X2,sK1) != iProver_top
% 2.92/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 2.92/0.99      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.92/0.99      | k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
% 2.92/0.99      | v1_funct_1(X1) != iProver_top ),
% 2.92/0.99      inference(global_propositional_subsumption,
% 2.92/0.99                [status(thm)],
% 2.92/0.99                [c_2482,c_32,c_33,c_34,c_35,c_23,c_91,c_0,c_2196]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2488,plain,
% 2.92/0.99      ( k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
% 2.92/0.99      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.92/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 2.92/0.99      | m1_subset_1(X2,sK1) != iProver_top
% 2.92/0.99      | v1_funct_1(X1) != iProver_top ),
% 2.92/0.99      inference(renaming,[status(thm)],[c_2487]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2498,plain,
% 2.92/0.99      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.92/0.99      | m1_subset_1(X0,sK1) != iProver_top
% 2.92/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 2.92/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.92/0.99      inference(equality_resolution,[status(thm)],[c_2488]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_37,plain,
% 2.92/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2553,plain,
% 2.92/0.99      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.92/0.99      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.92/0.99      inference(global_propositional_subsumption,
% 2.92/0.99                [status(thm)],
% 2.92/0.99                [c_2498,c_36,c_37]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2561,plain,
% 2.92/0.99      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.92/0.99      inference(superposition,[status(thm)],[c_1913,c_2553]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_22,negated_conjecture,
% 2.92/0.99      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
% 2.92/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2563,plain,
% 2.92/0.99      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.92/0.99      inference(demodulation,[status(thm)],[c_2561,c_22]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_5460,plain,
% 2.92/0.99      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 2.92/0.99      inference(global_propositional_subsumption,
% 2.92/0.99                [status(thm)],
% 2.92/0.99                [c_5459,c_2563]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_5467,plain,
% 2.92/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 2.92/0.99      inference(demodulation,[status(thm)],[c_5460,c_4871]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_11,plain,
% 2.92/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.92/0.99      | k1_xboole_0 = X1
% 2.92/0.99      | k1_xboole_0 = X0 ),
% 2.92/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_1919,plain,
% 2.92/0.99      ( k1_xboole_0 = X0
% 2.92/0.99      | k1_xboole_0 = X1
% 2.92/0.99      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 2.92/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_5842,plain,
% 2.92/0.99      ( sK1 = k1_xboole_0
% 2.92/0.99      | sK3 = k1_xboole_0
% 2.92/0.99      | v1_funct_2(sK3,sK1,k1_xboole_0) != iProver_top ),
% 2.92/0.99      inference(superposition,[status(thm)],[c_5467,c_1919]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_93,plain,
% 2.92/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2361,plain,
% 2.92/0.99      ( ~ v1_xboole_0(sK3) | k1_xboole_0 = sK3 ),
% 2.92/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2364,plain,
% 2.92/0.99      ( k1_xboole_0 = sK3 | v1_xboole_0(sK3) != iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_2361]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_1448,plain,( X0 = X0 ),theory(equality) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2427,plain,
% 2.92/0.99      ( sK3 = sK3 ),
% 2.92/0.99      inference(instantiation,[status(thm)],[c_1448]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_2868,plain,
% 2.92/0.99      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 2.92/0.99      inference(instantiation,[status(thm)],[c_1449]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_3761,plain,
% 2.92/0.99      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 2.92/0.99      inference(instantiation,[status(thm)],[c_2868]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_3762,plain,
% 2.92/0.99      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 2.92/0.99      inference(instantiation,[status(thm)],[c_3761]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_7,plain,
% 2.92/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.99      | ~ v1_xboole_0(X2)
% 2.92/0.99      | v1_xboole_0(X0) ),
% 2.92/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_1923,plain,
% 2.92/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.92/0.99      | v1_xboole_0(X2) != iProver_top
% 2.92/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.92/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_4878,plain,
% 2.92/0.99      ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top
% 2.92/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.92/0.99      inference(superposition,[status(thm)],[c_4871,c_1923]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_5465,plain,
% 2.92/0.99      ( v1_xboole_0(sK3) = iProver_top
% 2.92/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.92/0.99      inference(demodulation,[status(thm)],[c_5460,c_4878]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_5927,plain,
% 2.92/0.99      ( sK3 = k1_xboole_0 ),
% 2.92/0.99      inference(global_propositional_subsumption,
% 2.92/0.99                [status(thm)],
% 2.92/0.99                [c_5842,c_93,c_2364,c_2427,c_3762,c_5465]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_5938,plain,
% 2.92/0.99      ( k1_relat_1(k1_xboole_0) = sK1 ),
% 2.92/0.99      inference(demodulation,[status(thm)],[c_5927,c_4585]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_4,plain,
% 2.92/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.92/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(c_5977,plain,
% 2.92/0.99      ( sK1 = k1_xboole_0 ),
% 2.92/0.99      inference(light_normalisation,[status(thm)],[c_5938,c_4]) ).
% 2.92/0.99  
% 2.92/0.99  cnf(contradiction,plain,
% 2.92/0.99      ( $false ),
% 2.92/0.99      inference(minisat,[status(thm)],[c_5977,c_2196,c_0,c_91,c_23]) ).
% 2.92/0.99  
% 2.92/0.99  
% 2.92/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.92/0.99  
% 2.92/0.99  ------                               Statistics
% 2.92/0.99  
% 2.92/0.99  ------ General
% 2.92/0.99  
% 2.92/0.99  abstr_ref_over_cycles:                  0
% 2.92/0.99  abstr_ref_under_cycles:                 0
% 2.92/0.99  gc_basic_clause_elim:                   0
% 2.92/0.99  forced_gc_time:                         0
% 2.92/0.99  parsing_time:                           0.009
% 2.92/0.99  unif_index_cands_time:                  0.
% 2.92/0.99  unif_index_add_time:                    0.
% 2.92/0.99  orderings_time:                         0.
% 2.92/0.99  out_proof_time:                         0.011
% 2.92/0.99  total_time:                             0.19
% 2.92/0.99  num_of_symbols:                         55
% 2.92/0.99  num_of_terms:                           8987
% 2.92/0.99  
% 2.92/0.99  ------ Preprocessing
% 2.92/0.99  
% 2.92/0.99  num_of_splits:                          0
% 2.92/0.99  num_of_split_atoms:                     0
% 2.92/0.99  num_of_reused_defs:                     0
% 2.92/0.99  num_eq_ax_congr_red:                    5
% 2.92/0.99  num_of_sem_filtered_clauses:            1
% 2.92/0.99  num_of_subtypes:                        0
% 2.92/0.99  monotx_restored_types:                  0
% 2.92/0.99  sat_num_of_epr_types:                   0
% 2.92/0.99  sat_num_of_non_cyclic_types:            0
% 2.92/0.99  sat_guarded_non_collapsed_types:        0
% 2.92/0.99  num_pure_diseq_elim:                    0
% 2.92/0.99  simp_replaced_by:                       0
% 2.92/0.99  res_preprocessed:                       151
% 2.92/0.99  prep_upred:                             0
% 2.92/0.99  prep_unflattend:                        118
% 2.92/0.99  smt_new_axioms:                         0
% 2.92/0.99  pred_elim_cands:                        6
% 2.92/0.99  pred_elim:                              2
% 2.92/0.99  pred_elim_cl:                           2
% 2.92/0.99  pred_elim_cycles:                       7
% 2.92/0.99  merged_defs:                            0
% 2.92/0.99  merged_defs_ncl:                        0
% 2.92/0.99  bin_hyper_res:                          0
% 2.92/0.99  prep_cycles:                            4
% 2.92/0.99  pred_elim_time:                         0.018
% 2.92/0.99  splitting_time:                         0.
% 2.92/0.99  sem_filter_time:                        0.
% 2.92/0.99  monotx_time:                            0.
% 2.92/0.99  subtype_inf_time:                       0.
% 2.92/0.99  
% 2.92/0.99  ------ Problem properties
% 2.92/0.99  
% 2.92/0.99  clauses:                                29
% 2.92/0.99  conjectures:                            9
% 2.92/0.99  epr:                                    9
% 2.92/0.99  horn:                                   22
% 2.92/0.99  ground:                                 12
% 2.92/0.99  unary:                                  12
% 2.92/0.99  binary:                                 4
% 2.92/0.99  lits:                                   76
% 2.92/0.99  lits_eq:                                24
% 2.92/0.99  fd_pure:                                0
% 2.92/0.99  fd_pseudo:                              0
% 2.92/0.99  fd_cond:                                6
% 2.92/0.99  fd_pseudo_cond:                         0
% 2.92/0.99  ac_symbols:                             0
% 2.92/0.99  
% 2.92/0.99  ------ Propositional Solver
% 2.92/0.99  
% 2.92/0.99  prop_solver_calls:                      28
% 2.92/0.99  prop_fast_solver_calls:                 1402
% 2.92/0.99  smt_solver_calls:                       0
% 2.92/0.99  smt_fast_solver_calls:                  0
% 2.92/0.99  prop_num_of_clauses:                    1949
% 2.92/0.99  prop_preprocess_simplified:             5891
% 2.92/0.99  prop_fo_subsumed:                       54
% 2.92/0.99  prop_solver_time:                       0.
% 2.92/0.99  smt_solver_time:                        0.
% 2.92/0.99  smt_fast_solver_time:                   0.
% 2.92/0.99  prop_fast_solver_time:                  0.
% 2.92/0.99  prop_unsat_core_time:                   0.
% 2.92/0.99  
% 2.92/0.99  ------ QBF
% 2.92/0.99  
% 2.92/0.99  qbf_q_res:                              0
% 2.92/0.99  qbf_num_tautologies:                    0
% 2.92/0.99  qbf_prep_cycles:                        0
% 2.92/0.99  
% 2.92/0.99  ------ BMC1
% 2.92/0.99  
% 2.92/0.99  bmc1_current_bound:                     -1
% 2.92/0.99  bmc1_last_solved_bound:                 -1
% 2.92/0.99  bmc1_unsat_core_size:                   -1
% 2.92/0.99  bmc1_unsat_core_parents_size:           -1
% 2.92/0.99  bmc1_merge_next_fun:                    0
% 2.92/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.92/0.99  
% 2.92/0.99  ------ Instantiation
% 2.92/0.99  
% 2.92/0.99  inst_num_of_clauses:                    601
% 2.92/0.99  inst_num_in_passive:                    32
% 2.92/0.99  inst_num_in_active:                     362
% 2.92/0.99  inst_num_in_unprocessed:                207
% 2.92/0.99  inst_num_of_loops:                      370
% 2.92/0.99  inst_num_of_learning_restarts:          0
% 2.92/0.99  inst_num_moves_active_passive:          5
% 2.92/0.99  inst_lit_activity:                      0
% 2.92/0.99  inst_lit_activity_moves:                0
% 2.92/0.99  inst_num_tautologies:                   0
% 2.92/0.99  inst_num_prop_implied:                  0
% 2.92/0.99  inst_num_existing_simplified:           0
% 2.92/0.99  inst_num_eq_res_simplified:             0
% 2.92/0.99  inst_num_child_elim:                    0
% 2.92/0.99  inst_num_of_dismatching_blockings:      51
% 2.92/0.99  inst_num_of_non_proper_insts:           468
% 2.92/0.99  inst_num_of_duplicates:                 0
% 2.92/0.99  inst_inst_num_from_inst_to_res:         0
% 2.92/0.99  inst_dismatching_checking_time:         0.
% 2.92/0.99  
% 2.92/0.99  ------ Resolution
% 2.92/0.99  
% 2.92/0.99  res_num_of_clauses:                     0
% 2.92/0.99  res_num_in_passive:                     0
% 2.92/0.99  res_num_in_active:                      0
% 2.92/0.99  res_num_of_loops:                       155
% 2.92/0.99  res_forward_subset_subsumed:            48
% 2.92/0.99  res_backward_subset_subsumed:           2
% 2.92/0.99  res_forward_subsumed:                   2
% 2.92/0.99  res_backward_subsumed:                  0
% 2.92/0.99  res_forward_subsumption_resolution:     5
% 2.92/0.99  res_backward_subsumption_resolution:    0
% 2.92/0.99  res_clause_to_clause_subsumption:       222
% 2.92/0.99  res_orphan_elimination:                 0
% 2.92/0.99  res_tautology_del:                      61
% 2.92/0.99  res_num_eq_res_simplified:              0
% 2.92/0.99  res_num_sel_changes:                    0
% 2.92/0.99  res_moves_from_active_to_pass:          0
% 2.92/0.99  
% 2.92/0.99  ------ Superposition
% 2.92/0.99  
% 2.92/0.99  sup_time_total:                         0.
% 2.92/0.99  sup_time_generating:                    0.
% 2.92/0.99  sup_time_sim_full:                      0.
% 2.92/0.99  sup_time_sim_immed:                     0.
% 2.92/0.99  
% 2.92/0.99  sup_num_of_clauses:                     49
% 2.92/0.99  sup_num_in_active:                      31
% 2.92/0.99  sup_num_in_passive:                     18
% 2.92/0.99  sup_num_of_loops:                       73
% 2.92/0.99  sup_fw_superposition:                   27
% 2.92/0.99  sup_bw_superposition:                   23
% 2.92/0.99  sup_immediate_simplified:               30
% 2.92/0.99  sup_given_eliminated:                   0
% 2.92/0.99  comparisons_done:                       0
% 2.92/0.99  comparisons_avoided:                    3
% 2.92/0.99  
% 2.92/0.99  ------ Simplifications
% 2.92/0.99  
% 2.92/0.99  
% 2.92/0.99  sim_fw_subset_subsumed:                 6
% 2.92/0.99  sim_bw_subset_subsumed:                 2
% 2.92/0.99  sim_fw_subsumed:                        2
% 2.92/0.99  sim_bw_subsumed:                        0
% 2.92/0.99  sim_fw_subsumption_res:                 0
% 2.92/0.99  sim_bw_subsumption_res:                 0
% 2.92/0.99  sim_tautology_del:                      0
% 2.92/0.99  sim_eq_tautology_del:                   5
% 2.92/0.99  sim_eq_res_simp:                        0
% 2.92/0.99  sim_fw_demodulated:                     2
% 2.92/0.99  sim_bw_demodulated:                     48
% 2.92/0.99  sim_light_normalised:                   22
% 2.92/0.99  sim_joinable_taut:                      0
% 2.92/0.99  sim_joinable_simp:                      0
% 2.92/0.99  sim_ac_normalised:                      0
% 2.92/0.99  sim_smt_subsumption:                    0
% 2.92/0.99  
%------------------------------------------------------------------------------

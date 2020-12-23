%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:44 EST 2020

% Result     : Theorem 23.44s
% Output     : CNFRefutation 23.44s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 771 expanded)
%              Number of clauses        :  107 ( 205 expanded)
%              Number of leaves         :   24 ( 262 expanded)
%              Depth                    :   19
%              Number of atoms          :  702 (5798 expanded)
%              Number of equality atoms :  273 (1520 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
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
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
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
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f49,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f48])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK9) != k7_partfun1(X0,X4,k1_funct_1(X3,sK9))
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK9,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
              & k1_xboole_0 != X1
              & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK8),X5) != k7_partfun1(X0,sK8,k1_funct_1(X3,X5))
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK8))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
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
                ( k1_funct_1(k8_funct_2(X1,X2,X0,sK7,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK7,X5))
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK7),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK7,X1,X2)
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
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
                  ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,X3,X4),X5) != k7_partfun1(sK4,X4,k1_funct_1(X3,X5))
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

fof(f67,plain,
    ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9))
    & k1_xboole_0 != sK5
    & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    & m1_subset_1(sK9,sK5)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7)
    & ~ v1_xboole_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f49,f66,f65,f64,f63])).

fof(f113,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f67])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f114,plain,(
    m1_subset_1(sK9,sK5) ),
    inference(cnf_transformation,[],[f67])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f116,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f67])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f115,plain,(
    r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) ),
    inference(cnf_transformation,[],[f67])).

fof(f111,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f67])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f109,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f67])).

fof(f110,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f67])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f108,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f67])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f44])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f112,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f67])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f51,f52])).

fof(f69,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f16,axiom,(
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

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f18,axiom,(
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

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f100,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f117,plain,(
    k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_5041,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_23,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_5057,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6896,plain,
    ( v5_relat_1(sK8,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5041,c_5057])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK9,sK5) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_5042,plain,
    ( m1_subset_1(sK9,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_5074,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7026,plain,
    ( r2_hidden(sK9,sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5042,c_5074])).

cnf(c_56,plain,
    ( m1_subset_1(sK9,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_41,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_5137,plain,
    ( ~ v1_xboole_0(sK5)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5138,plain,
    ( k1_xboole_0 = sK5
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5137])).

cnf(c_5202,plain,
    ( ~ m1_subset_1(X0,sK5)
    | r2_hidden(X0,sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_5456,plain,
    ( ~ m1_subset_1(sK9,sK5)
    | r2_hidden(sK9,sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_5202])).

cnf(c_5457,plain,
    ( m1_subset_1(sK9,sK5) != iProver_top
    | r2_hidden(sK9,sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5456])).

cnf(c_7335,plain,
    ( r2_hidden(sK9,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7026,c_56,c_41,c_5138,c_5457])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_5056,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6905,plain,
    ( k1_relset_1(sK6,sK4,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_5041,c_5056])).

cnf(c_42,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_5043,plain,
    ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_7204,plain,
    ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relat_1(sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6905,c_5043])).

cnf(c_46,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_5039,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_5046,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_8666,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5039,c_5046])).

cnf(c_48,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_51,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_47,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_52,plain,
    ( v1_funct_2(sK7,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_49,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1253,plain,
    ( sK6 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_49])).

cnf(c_9287,plain,
    ( r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8666,c_51,c_52,c_1253])).

cnf(c_9288,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9287])).

cnf(c_9293,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK8)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7204,c_9288])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_5048,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_10367,plain,
    ( k1_relat_1(sK8) = k1_xboole_0
    | v1_funct_2(sK7,sK5,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k1_relat_1(sK8)) = iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_9293,c_5048])).

cnf(c_37,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_5044,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_6838,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,X0) = iProver_top
    | v1_funct_2(sK7,sK5,sK6) != iProver_top
    | r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5039,c_5044])).

cnf(c_8455,plain,
    ( r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top
    | v1_funct_2(sK7,sK5,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6838,c_51,c_52,c_1253])).

cnf(c_8456,plain,
    ( v1_funct_2(sK7,sK5,X0) = iProver_top
    | r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8455])).

cnf(c_8461,plain,
    ( v1_funct_2(sK7,sK5,k1_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7204,c_8456])).

cnf(c_14496,plain,
    ( r2_hidden(k1_funct_1(sK7,X0),k1_relat_1(sK8)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | k1_relat_1(sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10367,c_51,c_8461])).

cnf(c_14497,plain,
    ( k1_relat_1(sK8) = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k1_relat_1(sK8)) = iProver_top ),
    inference(renaming,[status(thm)],[c_14496])).

cnf(c_31,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_5050,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | v5_relat_1(X1,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_14504,plain,
    ( k7_partfun1(X0,sK8,k1_funct_1(sK7,X1)) = k1_funct_1(sK8,k1_funct_1(sK7,X1))
    | k1_relat_1(sK8) = k1_xboole_0
    | v5_relat_1(sK8,X0) != iProver_top
    | r2_hidden(X1,sK5) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_14497,c_5050])).

cnf(c_45,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_54,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_157,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_5058,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6443,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_5041,c_5058])).

cnf(c_6444,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_5039,c_5058])).

cnf(c_4065,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_12852,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(sK8))
    | k1_relat_1(sK8) != X0 ),
    inference(instantiation,[status(thm)],[c_4065])).

cnf(c_12858,plain,
    ( k1_relat_1(sK8) != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12852])).

cnf(c_12860,plain,
    ( k1_relat_1(sK8) != k1_xboole_0
    | v1_xboole_0(k1_relat_1(sK8)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12858])).

cnf(c_9418,plain,
    ( v5_relat_1(sK7,k1_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9293,c_5057])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_5079,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_5070,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_362,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_363,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_362])).

cnf(c_455,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_363])).

cnf(c_5035,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_7036,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5070,c_5035])).

cnf(c_14833,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5079,c_7036])).

cnf(c_18491,plain,
    ( v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k1_relat_1(sK8)) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9418,c_14833])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_5051,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8773,plain,
    ( k1_relset_1(sK5,sK6,sK7) = sK5
    | sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5039,c_5051])).

cnf(c_6906,plain,
    ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_5039,c_5056])).

cnf(c_8774,plain,
    ( k1_relat_1(sK7) = sK5
    | sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8773,c_6906])).

cnf(c_9435,plain,
    ( k1_relat_1(sK7) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8774,c_52,c_1253])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_5060,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_5078,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8933,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(k2_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5060,c_5078])).

cnf(c_18523,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9435,c_8933])).

cnf(c_19469,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18523,c_51,c_6444])).

cnf(c_19481,plain,
    ( v1_xboole_0(k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7335,c_19469])).

cnf(c_75905,plain,
    ( k7_partfun1(X0,sK8,k1_funct_1(sK7,X1)) = k1_funct_1(sK8,k1_funct_1(sK7,X1))
    | v5_relat_1(sK8,X0) != iProver_top
    | r2_hidden(X1,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14504,c_54,c_157,c_6443,c_6444,c_12860,c_18491,c_19481])).

cnf(c_75921,plain,
    ( k7_partfun1(X0,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | v5_relat_1(sK8,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7335,c_75905])).

cnf(c_76028,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
    inference(superposition,[status(thm)],[c_6896,c_75921])).

cnf(c_32,plain,
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
    inference(cnf_transformation,[],[f100])).

cnf(c_5195,plain,
    ( ~ v1_funct_2(X0,X1,sK6)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK6)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,X4)))
    | ~ r1_tarski(k2_relset_1(X1,sK6,X0),k1_relset_1(sK6,X4,X3))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(sK6)
    | k1_funct_1(k8_funct_2(X1,sK6,X4,X0,X3),X2) = k1_funct_1(X3,k1_funct_1(X0,X2))
    | k1_xboole_0 = X1 ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_5401,plain,
    ( ~ v1_funct_2(X0,sK5,sK6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ m1_subset_1(X3,sK5)
    | ~ r1_tarski(k2_relset_1(sK5,sK6,X0),k1_relset_1(sK6,X2,X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v1_xboole_0(sK6)
    | k1_funct_1(k8_funct_2(sK5,sK6,X2,X0,X1),X3) = k1_funct_1(X1,k1_funct_1(X0,X3))
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_5195])).

cnf(c_5748,plain,
    ( ~ v1_funct_2(X0,sK5,sK6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ m1_subset_1(sK9,sK5)
    | ~ r1_tarski(k2_relset_1(sK5,sK6,X0),k1_relset_1(sK6,X2,X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v1_xboole_0(sK6)
    | k1_funct_1(k8_funct_2(sK5,sK6,X2,X0,X1),sK9) = k1_funct_1(X1,k1_funct_1(X0,sK9))
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_5401])).

cnf(c_6322,plain,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,X1)))
    | ~ m1_subset_1(sK9,sK5)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,X1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK7)
    | v1_xboole_0(sK6)
    | k1_funct_1(k8_funct_2(sK5,sK6,X1,sK7,X0),sK9) = k1_funct_1(X0,k1_funct_1(sK7,sK9))
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_5748])).

cnf(c_7455,plain,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | ~ m1_subset_1(sK9,sK5)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK7)
    | v1_xboole_0(sK6)
    | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) = k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_6322])).

cnf(c_4064,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5134,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != X0
    | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != X0
    | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) = k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_4064])).

cnf(c_5233,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) = k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9))
    | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_5134])).

cnf(c_40,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) ),
    inference(cnf_transformation,[],[f117])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_76028,c_7455,c_5233,c_40,c_41,c_42,c_43,c_44,c_45,c_46,c_47,c_48,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:32:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.44/3.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.44/3.49  
% 23.44/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.44/3.49  
% 23.44/3.49  ------  iProver source info
% 23.44/3.49  
% 23.44/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.44/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.44/3.49  git: non_committed_changes: false
% 23.44/3.49  git: last_make_outside_of_git: false
% 23.44/3.49  
% 23.44/3.49  ------ 
% 23.44/3.49  
% 23.44/3.49  ------ Input Options
% 23.44/3.49  
% 23.44/3.49  --out_options                           all
% 23.44/3.49  --tptp_safe_out                         true
% 23.44/3.49  --problem_path                          ""
% 23.44/3.49  --include_path                          ""
% 23.44/3.49  --clausifier                            res/vclausify_rel
% 23.44/3.49  --clausifier_options                    ""
% 23.44/3.49  --stdin                                 false
% 23.44/3.49  --stats_out                             all
% 23.44/3.49  
% 23.44/3.49  ------ General Options
% 23.44/3.49  
% 23.44/3.49  --fof                                   false
% 23.44/3.49  --time_out_real                         305.
% 23.44/3.49  --time_out_virtual                      -1.
% 23.44/3.49  --symbol_type_check                     false
% 23.44/3.49  --clausify_out                          false
% 23.44/3.49  --sig_cnt_out                           false
% 23.44/3.49  --trig_cnt_out                          false
% 23.44/3.49  --trig_cnt_out_tolerance                1.
% 23.44/3.49  --trig_cnt_out_sk_spl                   false
% 23.44/3.49  --abstr_cl_out                          false
% 23.44/3.49  
% 23.44/3.49  ------ Global Options
% 23.44/3.49  
% 23.44/3.49  --schedule                              default
% 23.44/3.49  --add_important_lit                     false
% 23.44/3.49  --prop_solver_per_cl                    1000
% 23.44/3.49  --min_unsat_core                        false
% 23.44/3.49  --soft_assumptions                      false
% 23.44/3.49  --soft_lemma_size                       3
% 23.44/3.49  --prop_impl_unit_size                   0
% 23.44/3.49  --prop_impl_unit                        []
% 23.44/3.49  --share_sel_clauses                     true
% 23.44/3.49  --reset_solvers                         false
% 23.44/3.49  --bc_imp_inh                            [conj_cone]
% 23.44/3.49  --conj_cone_tolerance                   3.
% 23.44/3.49  --extra_neg_conj                        none
% 23.44/3.49  --large_theory_mode                     true
% 23.44/3.49  --prolific_symb_bound                   200
% 23.44/3.49  --lt_threshold                          2000
% 23.44/3.49  --clause_weak_htbl                      true
% 23.44/3.49  --gc_record_bc_elim                     false
% 23.44/3.49  
% 23.44/3.49  ------ Preprocessing Options
% 23.44/3.49  
% 23.44/3.49  --preprocessing_flag                    true
% 23.44/3.49  --time_out_prep_mult                    0.1
% 23.44/3.49  --splitting_mode                        input
% 23.44/3.49  --splitting_grd                         true
% 23.44/3.49  --splitting_cvd                         false
% 23.44/3.49  --splitting_cvd_svl                     false
% 23.44/3.49  --splitting_nvd                         32
% 23.44/3.49  --sub_typing                            true
% 23.44/3.49  --prep_gs_sim                           true
% 23.44/3.49  --prep_unflatten                        true
% 23.44/3.49  --prep_res_sim                          true
% 23.44/3.49  --prep_upred                            true
% 23.44/3.49  --prep_sem_filter                       exhaustive
% 23.44/3.49  --prep_sem_filter_out                   false
% 23.44/3.49  --pred_elim                             true
% 23.44/3.49  --res_sim_input                         true
% 23.44/3.49  --eq_ax_congr_red                       true
% 23.44/3.49  --pure_diseq_elim                       true
% 23.44/3.49  --brand_transform                       false
% 23.44/3.49  --non_eq_to_eq                          false
% 23.44/3.49  --prep_def_merge                        true
% 23.44/3.49  --prep_def_merge_prop_impl              false
% 23.44/3.49  --prep_def_merge_mbd                    true
% 23.44/3.49  --prep_def_merge_tr_red                 false
% 23.44/3.49  --prep_def_merge_tr_cl                  false
% 23.44/3.49  --smt_preprocessing                     true
% 23.44/3.49  --smt_ac_axioms                         fast
% 23.44/3.49  --preprocessed_out                      false
% 23.44/3.49  --preprocessed_stats                    false
% 23.44/3.49  
% 23.44/3.49  ------ Abstraction refinement Options
% 23.44/3.49  
% 23.44/3.49  --abstr_ref                             []
% 23.44/3.49  --abstr_ref_prep                        false
% 23.44/3.49  --abstr_ref_until_sat                   false
% 23.44/3.49  --abstr_ref_sig_restrict                funpre
% 23.44/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.44/3.49  --abstr_ref_under                       []
% 23.44/3.49  
% 23.44/3.49  ------ SAT Options
% 23.44/3.49  
% 23.44/3.49  --sat_mode                              false
% 23.44/3.49  --sat_fm_restart_options                ""
% 23.44/3.49  --sat_gr_def                            false
% 23.44/3.49  --sat_epr_types                         true
% 23.44/3.49  --sat_non_cyclic_types                  false
% 23.44/3.49  --sat_finite_models                     false
% 23.44/3.49  --sat_fm_lemmas                         false
% 23.44/3.49  --sat_fm_prep                           false
% 23.44/3.49  --sat_fm_uc_incr                        true
% 23.44/3.49  --sat_out_model                         small
% 23.44/3.49  --sat_out_clauses                       false
% 23.44/3.49  
% 23.44/3.49  ------ QBF Options
% 23.44/3.49  
% 23.44/3.49  --qbf_mode                              false
% 23.44/3.49  --qbf_elim_univ                         false
% 23.44/3.49  --qbf_dom_inst                          none
% 23.44/3.49  --qbf_dom_pre_inst                      false
% 23.44/3.49  --qbf_sk_in                             false
% 23.44/3.49  --qbf_pred_elim                         true
% 23.44/3.49  --qbf_split                             512
% 23.44/3.49  
% 23.44/3.49  ------ BMC1 Options
% 23.44/3.49  
% 23.44/3.49  --bmc1_incremental                      false
% 23.44/3.49  --bmc1_axioms                           reachable_all
% 23.44/3.49  --bmc1_min_bound                        0
% 23.44/3.49  --bmc1_max_bound                        -1
% 23.44/3.49  --bmc1_max_bound_default                -1
% 23.44/3.49  --bmc1_symbol_reachability              true
% 23.44/3.49  --bmc1_property_lemmas                  false
% 23.44/3.49  --bmc1_k_induction                      false
% 23.44/3.49  --bmc1_non_equiv_states                 false
% 23.44/3.49  --bmc1_deadlock                         false
% 23.44/3.49  --bmc1_ucm                              false
% 23.44/3.49  --bmc1_add_unsat_core                   none
% 23.44/3.49  --bmc1_unsat_core_children              false
% 23.44/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.44/3.49  --bmc1_out_stat                         full
% 23.44/3.49  --bmc1_ground_init                      false
% 23.44/3.49  --bmc1_pre_inst_next_state              false
% 23.44/3.49  --bmc1_pre_inst_state                   false
% 23.44/3.49  --bmc1_pre_inst_reach_state             false
% 23.44/3.49  --bmc1_out_unsat_core                   false
% 23.44/3.49  --bmc1_aig_witness_out                  false
% 23.44/3.49  --bmc1_verbose                          false
% 23.44/3.49  --bmc1_dump_clauses_tptp                false
% 23.44/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.44/3.49  --bmc1_dump_file                        -
% 23.44/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.44/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.44/3.49  --bmc1_ucm_extend_mode                  1
% 23.44/3.49  --bmc1_ucm_init_mode                    2
% 23.44/3.49  --bmc1_ucm_cone_mode                    none
% 23.44/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.44/3.49  --bmc1_ucm_relax_model                  4
% 23.44/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.44/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.44/3.49  --bmc1_ucm_layered_model                none
% 23.44/3.49  --bmc1_ucm_max_lemma_size               10
% 23.44/3.49  
% 23.44/3.49  ------ AIG Options
% 23.44/3.49  
% 23.44/3.49  --aig_mode                              false
% 23.44/3.49  
% 23.44/3.49  ------ Instantiation Options
% 23.44/3.49  
% 23.44/3.49  --instantiation_flag                    true
% 23.44/3.49  --inst_sos_flag                         true
% 23.44/3.49  --inst_sos_phase                        true
% 23.44/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.44/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.44/3.49  --inst_lit_sel_side                     num_symb
% 23.44/3.49  --inst_solver_per_active                1400
% 23.44/3.49  --inst_solver_calls_frac                1.
% 23.44/3.49  --inst_passive_queue_type               priority_queues
% 23.44/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.44/3.49  --inst_passive_queues_freq              [25;2]
% 23.44/3.49  --inst_dismatching                      true
% 23.44/3.49  --inst_eager_unprocessed_to_passive     true
% 23.44/3.49  --inst_prop_sim_given                   true
% 23.44/3.49  --inst_prop_sim_new                     false
% 23.44/3.49  --inst_subs_new                         false
% 23.44/3.49  --inst_eq_res_simp                      false
% 23.44/3.49  --inst_subs_given                       false
% 23.44/3.49  --inst_orphan_elimination               true
% 23.44/3.49  --inst_learning_loop_flag               true
% 23.44/3.49  --inst_learning_start                   3000
% 23.44/3.49  --inst_learning_factor                  2
% 23.44/3.49  --inst_start_prop_sim_after_learn       3
% 23.44/3.49  --inst_sel_renew                        solver
% 23.44/3.49  --inst_lit_activity_flag                true
% 23.44/3.49  --inst_restr_to_given                   false
% 23.44/3.49  --inst_activity_threshold               500
% 23.44/3.49  --inst_out_proof                        true
% 23.44/3.49  
% 23.44/3.49  ------ Resolution Options
% 23.44/3.49  
% 23.44/3.49  --resolution_flag                       true
% 23.44/3.49  --res_lit_sel                           adaptive
% 23.44/3.49  --res_lit_sel_side                      none
% 23.44/3.49  --res_ordering                          kbo
% 23.44/3.49  --res_to_prop_solver                    active
% 23.44/3.49  --res_prop_simpl_new                    false
% 23.44/3.49  --res_prop_simpl_given                  true
% 23.44/3.49  --res_passive_queue_type                priority_queues
% 23.44/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.44/3.49  --res_passive_queues_freq               [15;5]
% 23.44/3.49  --res_forward_subs                      full
% 23.44/3.49  --res_backward_subs                     full
% 23.44/3.49  --res_forward_subs_resolution           true
% 23.44/3.49  --res_backward_subs_resolution          true
% 23.44/3.49  --res_orphan_elimination                true
% 23.44/3.49  --res_time_limit                        2.
% 23.44/3.49  --res_out_proof                         true
% 23.44/3.49  
% 23.44/3.49  ------ Superposition Options
% 23.44/3.49  
% 23.44/3.49  --superposition_flag                    true
% 23.44/3.49  --sup_passive_queue_type                priority_queues
% 23.44/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.44/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.44/3.49  --demod_completeness_check              fast
% 23.44/3.49  --demod_use_ground                      true
% 23.44/3.49  --sup_to_prop_solver                    passive
% 23.44/3.49  --sup_prop_simpl_new                    true
% 23.44/3.49  --sup_prop_simpl_given                  true
% 23.44/3.49  --sup_fun_splitting                     true
% 23.44/3.49  --sup_smt_interval                      50000
% 23.44/3.49  
% 23.44/3.49  ------ Superposition Simplification Setup
% 23.44/3.49  
% 23.44/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.44/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.44/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.44/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.44/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.44/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.44/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.44/3.49  --sup_immed_triv                        [TrivRules]
% 23.44/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.44/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.44/3.49  --sup_immed_bw_main                     []
% 23.44/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.44/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.44/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.44/3.49  --sup_input_bw                          []
% 23.44/3.49  
% 23.44/3.49  ------ Combination Options
% 23.44/3.49  
% 23.44/3.49  --comb_res_mult                         3
% 23.44/3.49  --comb_sup_mult                         2
% 23.44/3.49  --comb_inst_mult                        10
% 23.44/3.49  
% 23.44/3.49  ------ Debug Options
% 23.44/3.49  
% 23.44/3.49  --dbg_backtrace                         false
% 23.44/3.49  --dbg_dump_prop_clauses                 false
% 23.44/3.49  --dbg_dump_prop_clauses_file            -
% 23.44/3.49  --dbg_out_stat                          false
% 23.44/3.49  ------ Parsing...
% 23.44/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.44/3.49  
% 23.44/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.44/3.49  
% 23.44/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.44/3.49  
% 23.44/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.44/3.49  ------ Proving...
% 23.44/3.49  ------ Problem Properties 
% 23.44/3.49  
% 23.44/3.49  
% 23.44/3.49  clauses                                 48
% 23.44/3.49  conjectures                             10
% 23.44/3.49  EPR                                     15
% 23.44/3.49  Horn                                    35
% 23.44/3.49  unary                                   12
% 23.44/3.49  binary                                  11
% 23.44/3.49  lits                                    150
% 23.44/3.49  lits eq                                 26
% 23.44/3.49  fd_pure                                 0
% 23.44/3.49  fd_pseudo                               0
% 23.44/3.49  fd_cond                                 8
% 23.44/3.49  fd_pseudo_cond                          4
% 23.44/3.49  AC symbols                              0
% 23.44/3.49  
% 23.44/3.49  ------ Schedule dynamic 5 is on 
% 23.44/3.49  
% 23.44/3.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.44/3.49  
% 23.44/3.49  
% 23.44/3.49  ------ 
% 23.44/3.49  Current options:
% 23.44/3.49  ------ 
% 23.44/3.49  
% 23.44/3.49  ------ Input Options
% 23.44/3.49  
% 23.44/3.49  --out_options                           all
% 23.44/3.49  --tptp_safe_out                         true
% 23.44/3.49  --problem_path                          ""
% 23.44/3.49  --include_path                          ""
% 23.44/3.49  --clausifier                            res/vclausify_rel
% 23.44/3.49  --clausifier_options                    ""
% 23.44/3.49  --stdin                                 false
% 23.44/3.49  --stats_out                             all
% 23.44/3.49  
% 23.44/3.49  ------ General Options
% 23.44/3.49  
% 23.44/3.49  --fof                                   false
% 23.44/3.49  --time_out_real                         305.
% 23.44/3.49  --time_out_virtual                      -1.
% 23.44/3.49  --symbol_type_check                     false
% 23.44/3.49  --clausify_out                          false
% 23.44/3.49  --sig_cnt_out                           false
% 23.44/3.49  --trig_cnt_out                          false
% 23.44/3.49  --trig_cnt_out_tolerance                1.
% 23.44/3.49  --trig_cnt_out_sk_spl                   false
% 23.44/3.49  --abstr_cl_out                          false
% 23.44/3.49  
% 23.44/3.49  ------ Global Options
% 23.44/3.49  
% 23.44/3.49  --schedule                              default
% 23.44/3.49  --add_important_lit                     false
% 23.44/3.49  --prop_solver_per_cl                    1000
% 23.44/3.49  --min_unsat_core                        false
% 23.44/3.49  --soft_assumptions                      false
% 23.44/3.49  --soft_lemma_size                       3
% 23.44/3.49  --prop_impl_unit_size                   0
% 23.44/3.49  --prop_impl_unit                        []
% 23.44/3.49  --share_sel_clauses                     true
% 23.44/3.49  --reset_solvers                         false
% 23.44/3.49  --bc_imp_inh                            [conj_cone]
% 23.44/3.49  --conj_cone_tolerance                   3.
% 23.44/3.49  --extra_neg_conj                        none
% 23.44/3.49  --large_theory_mode                     true
% 23.44/3.49  --prolific_symb_bound                   200
% 23.44/3.49  --lt_threshold                          2000
% 23.44/3.49  --clause_weak_htbl                      true
% 23.44/3.49  --gc_record_bc_elim                     false
% 23.44/3.49  
% 23.44/3.49  ------ Preprocessing Options
% 23.44/3.49  
% 23.44/3.49  --preprocessing_flag                    true
% 23.44/3.49  --time_out_prep_mult                    0.1
% 23.44/3.49  --splitting_mode                        input
% 23.44/3.49  --splitting_grd                         true
% 23.44/3.49  --splitting_cvd                         false
% 23.44/3.49  --splitting_cvd_svl                     false
% 23.44/3.49  --splitting_nvd                         32
% 23.44/3.49  --sub_typing                            true
% 23.44/3.49  --prep_gs_sim                           true
% 23.44/3.49  --prep_unflatten                        true
% 23.44/3.49  --prep_res_sim                          true
% 23.44/3.49  --prep_upred                            true
% 23.44/3.49  --prep_sem_filter                       exhaustive
% 23.44/3.49  --prep_sem_filter_out                   false
% 23.44/3.49  --pred_elim                             true
% 23.44/3.49  --res_sim_input                         true
% 23.44/3.49  --eq_ax_congr_red                       true
% 23.44/3.49  --pure_diseq_elim                       true
% 23.44/3.49  --brand_transform                       false
% 23.44/3.49  --non_eq_to_eq                          false
% 23.44/3.49  --prep_def_merge                        true
% 23.44/3.49  --prep_def_merge_prop_impl              false
% 23.44/3.49  --prep_def_merge_mbd                    true
% 23.44/3.49  --prep_def_merge_tr_red                 false
% 23.44/3.49  --prep_def_merge_tr_cl                  false
% 23.44/3.49  --smt_preprocessing                     true
% 23.44/3.49  --smt_ac_axioms                         fast
% 23.44/3.49  --preprocessed_out                      false
% 23.44/3.49  --preprocessed_stats                    false
% 23.44/3.49  
% 23.44/3.49  ------ Abstraction refinement Options
% 23.44/3.49  
% 23.44/3.49  --abstr_ref                             []
% 23.44/3.49  --abstr_ref_prep                        false
% 23.44/3.49  --abstr_ref_until_sat                   false
% 23.44/3.49  --abstr_ref_sig_restrict                funpre
% 23.44/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.44/3.49  --abstr_ref_under                       []
% 23.44/3.49  
% 23.44/3.49  ------ SAT Options
% 23.44/3.49  
% 23.44/3.49  --sat_mode                              false
% 23.44/3.49  --sat_fm_restart_options                ""
% 23.44/3.49  --sat_gr_def                            false
% 23.44/3.49  --sat_epr_types                         true
% 23.44/3.49  --sat_non_cyclic_types                  false
% 23.44/3.49  --sat_finite_models                     false
% 23.44/3.49  --sat_fm_lemmas                         false
% 23.44/3.49  --sat_fm_prep                           false
% 23.44/3.49  --sat_fm_uc_incr                        true
% 23.44/3.49  --sat_out_model                         small
% 23.44/3.49  --sat_out_clauses                       false
% 23.44/3.49  
% 23.44/3.49  ------ QBF Options
% 23.44/3.49  
% 23.44/3.49  --qbf_mode                              false
% 23.44/3.49  --qbf_elim_univ                         false
% 23.44/3.49  --qbf_dom_inst                          none
% 23.44/3.49  --qbf_dom_pre_inst                      false
% 23.44/3.49  --qbf_sk_in                             false
% 23.44/3.49  --qbf_pred_elim                         true
% 23.44/3.49  --qbf_split                             512
% 23.44/3.49  
% 23.44/3.49  ------ BMC1 Options
% 23.44/3.49  
% 23.44/3.49  --bmc1_incremental                      false
% 23.44/3.49  --bmc1_axioms                           reachable_all
% 23.44/3.49  --bmc1_min_bound                        0
% 23.44/3.49  --bmc1_max_bound                        -1
% 23.44/3.49  --bmc1_max_bound_default                -1
% 23.44/3.49  --bmc1_symbol_reachability              true
% 23.44/3.49  --bmc1_property_lemmas                  false
% 23.44/3.49  --bmc1_k_induction                      false
% 23.44/3.49  --bmc1_non_equiv_states                 false
% 23.44/3.49  --bmc1_deadlock                         false
% 23.44/3.49  --bmc1_ucm                              false
% 23.44/3.49  --bmc1_add_unsat_core                   none
% 23.44/3.49  --bmc1_unsat_core_children              false
% 23.44/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.44/3.49  --bmc1_out_stat                         full
% 23.44/3.49  --bmc1_ground_init                      false
% 23.44/3.49  --bmc1_pre_inst_next_state              false
% 23.44/3.49  --bmc1_pre_inst_state                   false
% 23.44/3.49  --bmc1_pre_inst_reach_state             false
% 23.44/3.49  --bmc1_out_unsat_core                   false
% 23.44/3.49  --bmc1_aig_witness_out                  false
% 23.44/3.49  --bmc1_verbose                          false
% 23.44/3.49  --bmc1_dump_clauses_tptp                false
% 23.44/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.44/3.49  --bmc1_dump_file                        -
% 23.44/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.44/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.44/3.49  --bmc1_ucm_extend_mode                  1
% 23.44/3.49  --bmc1_ucm_init_mode                    2
% 23.44/3.49  --bmc1_ucm_cone_mode                    none
% 23.44/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.44/3.49  --bmc1_ucm_relax_model                  4
% 23.44/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.44/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.44/3.49  --bmc1_ucm_layered_model                none
% 23.44/3.49  --bmc1_ucm_max_lemma_size               10
% 23.44/3.49  
% 23.44/3.49  ------ AIG Options
% 23.44/3.49  
% 23.44/3.49  --aig_mode                              false
% 23.44/3.49  
% 23.44/3.49  ------ Instantiation Options
% 23.44/3.49  
% 23.44/3.49  --instantiation_flag                    true
% 23.44/3.49  --inst_sos_flag                         true
% 23.44/3.49  --inst_sos_phase                        true
% 23.44/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.44/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.44/3.49  --inst_lit_sel_side                     none
% 23.44/3.49  --inst_solver_per_active                1400
% 23.44/3.49  --inst_solver_calls_frac                1.
% 23.44/3.49  --inst_passive_queue_type               priority_queues
% 23.44/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.44/3.49  --inst_passive_queues_freq              [25;2]
% 23.44/3.49  --inst_dismatching                      true
% 23.44/3.49  --inst_eager_unprocessed_to_passive     true
% 23.44/3.49  --inst_prop_sim_given                   true
% 23.44/3.49  --inst_prop_sim_new                     false
% 23.44/3.49  --inst_subs_new                         false
% 23.44/3.49  --inst_eq_res_simp                      false
% 23.44/3.49  --inst_subs_given                       false
% 23.44/3.49  --inst_orphan_elimination               true
% 23.44/3.49  --inst_learning_loop_flag               true
% 23.44/3.49  --inst_learning_start                   3000
% 23.44/3.49  --inst_learning_factor                  2
% 23.44/3.49  --inst_start_prop_sim_after_learn       3
% 23.44/3.49  --inst_sel_renew                        solver
% 23.44/3.49  --inst_lit_activity_flag                true
% 23.44/3.49  --inst_restr_to_given                   false
% 23.44/3.49  --inst_activity_threshold               500
% 23.44/3.49  --inst_out_proof                        true
% 23.44/3.49  
% 23.44/3.49  ------ Resolution Options
% 23.44/3.49  
% 23.44/3.49  --resolution_flag                       false
% 23.44/3.49  --res_lit_sel                           adaptive
% 23.44/3.49  --res_lit_sel_side                      none
% 23.44/3.49  --res_ordering                          kbo
% 23.44/3.49  --res_to_prop_solver                    active
% 23.44/3.49  --res_prop_simpl_new                    false
% 23.44/3.49  --res_prop_simpl_given                  true
% 23.44/3.49  --res_passive_queue_type                priority_queues
% 23.44/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.44/3.49  --res_passive_queues_freq               [15;5]
% 23.44/3.49  --res_forward_subs                      full
% 23.44/3.49  --res_backward_subs                     full
% 23.44/3.49  --res_forward_subs_resolution           true
% 23.44/3.49  --res_backward_subs_resolution          true
% 23.44/3.49  --res_orphan_elimination                true
% 23.44/3.49  --res_time_limit                        2.
% 23.44/3.49  --res_out_proof                         true
% 23.44/3.49  
% 23.44/3.49  ------ Superposition Options
% 23.44/3.49  
% 23.44/3.49  --superposition_flag                    true
% 23.44/3.49  --sup_passive_queue_type                priority_queues
% 23.44/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.44/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.44/3.49  --demod_completeness_check              fast
% 23.44/3.49  --demod_use_ground                      true
% 23.44/3.49  --sup_to_prop_solver                    passive
% 23.44/3.49  --sup_prop_simpl_new                    true
% 23.44/3.49  --sup_prop_simpl_given                  true
% 23.44/3.49  --sup_fun_splitting                     true
% 23.44/3.49  --sup_smt_interval                      50000
% 23.44/3.49  
% 23.44/3.49  ------ Superposition Simplification Setup
% 23.44/3.49  
% 23.44/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.44/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.44/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.44/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.44/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.44/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.44/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.44/3.49  --sup_immed_triv                        [TrivRules]
% 23.44/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.44/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.44/3.49  --sup_immed_bw_main                     []
% 23.44/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.44/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.44/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.44/3.49  --sup_input_bw                          []
% 23.44/3.49  
% 23.44/3.49  ------ Combination Options
% 23.44/3.49  
% 23.44/3.49  --comb_res_mult                         3
% 23.44/3.49  --comb_sup_mult                         2
% 23.44/3.49  --comb_inst_mult                        10
% 23.44/3.49  
% 23.44/3.49  ------ Debug Options
% 23.44/3.49  
% 23.44/3.49  --dbg_backtrace                         false
% 23.44/3.49  --dbg_dump_prop_clauses                 false
% 23.44/3.49  --dbg_dump_prop_clauses_file            -
% 23.44/3.49  --dbg_out_stat                          false
% 23.44/3.49  
% 23.44/3.49  
% 23.44/3.49  
% 23.44/3.49  
% 23.44/3.49  ------ Proving...
% 23.44/3.49  
% 23.44/3.49  
% 23.44/3.49  % SZS status Theorem for theBenchmark.p
% 23.44/3.49  
% 23.44/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.44/3.49  
% 23.44/3.49  fof(f21,conjecture,(
% 23.44/3.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 23.44/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.49  
% 23.44/3.49  fof(f22,negated_conjecture,(
% 23.44/3.49    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 23.44/3.49    inference(negated_conjecture,[],[f21])).
% 23.44/3.49  
% 23.44/3.49  fof(f48,plain,(
% 23.44/3.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 23.44/3.49    inference(ennf_transformation,[],[f22])).
% 23.44/3.49  
% 23.44/3.49  fof(f49,plain,(
% 23.44/3.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 23.44/3.49    inference(flattening,[],[f48])).
% 23.44/3.49  
% 23.44/3.49  fof(f66,plain,(
% 23.44/3.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK9) != k7_partfun1(X0,X4,k1_funct_1(X3,sK9)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK9,X1))) )),
% 23.44/3.49    introduced(choice_axiom,[])).
% 23.44/3.49  
% 23.44/3.49  fof(f65,plain,(
% 23.44/3.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK8),X5) != k7_partfun1(X0,sK8,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK8)) & m1_subset_1(X5,X1)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK8))) )),
% 23.44/3.49    introduced(choice_axiom,[])).
% 23.44/3.49  
% 23.44/3.49  fof(f64,plain,(
% 23.44/3.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK7,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK7,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK7),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK7,X1,X2) & v1_funct_1(sK7))) )),
% 23.44/3.49    introduced(choice_axiom,[])).
% 23.44/3.49  
% 23.44/3.49  fof(f63,plain,(
% 23.44/3.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK5,sK6,sK4,X3,X4),X5) != k7_partfun1(sK4,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,X3),k1_relset_1(sK6,sK4,X4)) & m1_subset_1(X5,sK5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) & ~v1_xboole_0(sK6))),
% 23.44/3.49    introduced(choice_axiom,[])).
% 23.44/3.49  
% 23.44/3.49  fof(f67,plain,(
% 23.44/3.49    (((k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) & m1_subset_1(sK9,sK5)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)) & ~v1_xboole_0(sK6)),
% 23.44/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f49,f66,f65,f64,f63])).
% 23.44/3.49  
% 23.44/3.49  fof(f113,plain,(
% 23.44/3.49    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))),
% 23.44/3.49    inference(cnf_transformation,[],[f67])).
% 23.44/3.49  
% 23.44/3.49  fof(f14,axiom,(
% 23.44/3.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 23.44/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.49  
% 23.44/3.49  fof(f23,plain,(
% 23.44/3.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 23.44/3.49    inference(pure_predicate_removal,[],[f14])).
% 23.44/3.49  
% 23.44/3.49  fof(f36,plain,(
% 23.44/3.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.44/3.49    inference(ennf_transformation,[],[f23])).
% 23.44/3.49  
% 23.44/3.49  fof(f91,plain,(
% 23.44/3.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.44/3.49    inference(cnf_transformation,[],[f36])).
% 23.44/3.49  
% 23.44/3.49  fof(f114,plain,(
% 23.44/3.49    m1_subset_1(sK9,sK5)),
% 23.44/3.49    inference(cnf_transformation,[],[f67])).
% 23.44/3.49  
% 23.44/3.49  fof(f5,axiom,(
% 23.44/3.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 23.44/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.49  
% 23.44/3.49  fof(f25,plain,(
% 23.44/3.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 23.44/3.49    inference(ennf_transformation,[],[f5])).
% 23.44/3.49  
% 23.44/3.49  fof(f26,plain,(
% 23.44/3.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 23.44/3.49    inference(flattening,[],[f25])).
% 23.44/3.49  
% 23.44/3.49  fof(f73,plain,(
% 23.44/3.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 23.44/3.49    inference(cnf_transformation,[],[f26])).
% 23.44/3.49  
% 23.44/3.49  fof(f116,plain,(
% 23.44/3.49    k1_xboole_0 != sK5),
% 23.44/3.49    inference(cnf_transformation,[],[f67])).
% 23.44/3.49  
% 23.44/3.49  fof(f3,axiom,(
% 23.44/3.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 23.44/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.49  
% 23.44/3.49  fof(f24,plain,(
% 23.44/3.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 23.44/3.49    inference(ennf_transformation,[],[f3])).
% 23.44/3.49  
% 23.44/3.49  fof(f71,plain,(
% 23.44/3.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 23.44/3.49    inference(cnf_transformation,[],[f24])).
% 23.44/3.49  
% 23.44/3.49  fof(f15,axiom,(
% 23.44/3.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 23.44/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.49  
% 23.44/3.49  fof(f37,plain,(
% 23.44/3.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.44/3.49    inference(ennf_transformation,[],[f15])).
% 23.44/3.49  
% 23.44/3.49  fof(f92,plain,(
% 23.44/3.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.44/3.49    inference(cnf_transformation,[],[f37])).
% 23.44/3.49  
% 23.44/3.49  fof(f115,plain,(
% 23.44/3.49    r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))),
% 23.44/3.49    inference(cnf_transformation,[],[f67])).
% 23.44/3.49  
% 23.44/3.49  fof(f111,plain,(
% 23.44/3.49    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 23.44/3.49    inference(cnf_transformation,[],[f67])).
% 23.44/3.49  
% 23.44/3.49  fof(f20,axiom,(
% 23.44/3.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 23.44/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.49  
% 23.44/3.49  fof(f46,plain,(
% 23.44/3.49    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 23.44/3.49    inference(ennf_transformation,[],[f20])).
% 23.44/3.49  
% 23.44/3.49  fof(f47,plain,(
% 23.44/3.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 23.44/3.49    inference(flattening,[],[f46])).
% 23.44/3.49  
% 23.44/3.49  fof(f106,plain,(
% 23.44/3.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 23.44/3.49    inference(cnf_transformation,[],[f47])).
% 23.44/3.49  
% 23.44/3.49  fof(f109,plain,(
% 23.44/3.49    v1_funct_1(sK7)),
% 23.44/3.49    inference(cnf_transformation,[],[f67])).
% 23.44/3.49  
% 23.44/3.49  fof(f110,plain,(
% 23.44/3.49    v1_funct_2(sK7,sK5,sK6)),
% 23.44/3.49    inference(cnf_transformation,[],[f67])).
% 23.44/3.49  
% 23.44/3.49  fof(f2,axiom,(
% 23.44/3.49    v1_xboole_0(k1_xboole_0)),
% 23.44/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.49  
% 23.44/3.49  fof(f70,plain,(
% 23.44/3.49    v1_xboole_0(k1_xboole_0)),
% 23.44/3.49    inference(cnf_transformation,[],[f2])).
% 23.44/3.49  
% 23.44/3.49  fof(f108,plain,(
% 23.44/3.49    ~v1_xboole_0(sK6)),
% 23.44/3.49    inference(cnf_transformation,[],[f67])).
% 23.44/3.49  
% 23.44/3.49  fof(f19,axiom,(
% 23.44/3.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 23.44/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.49  
% 23.44/3.49  fof(f44,plain,(
% 23.44/3.49    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 23.44/3.49    inference(ennf_transformation,[],[f19])).
% 23.44/3.49  
% 23.44/3.49  fof(f45,plain,(
% 23.44/3.49    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 23.44/3.49    inference(flattening,[],[f44])).
% 23.44/3.49  
% 23.44/3.49  fof(f101,plain,(
% 23.44/3.49    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 23.44/3.49    inference(cnf_transformation,[],[f45])).
% 23.44/3.49  
% 23.44/3.49  fof(f104,plain,(
% 23.44/3.49    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 23.44/3.49    inference(cnf_transformation,[],[f47])).
% 23.44/3.49  
% 23.44/3.49  fof(f17,axiom,(
% 23.44/3.49    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 23.44/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.49  
% 23.44/3.49  fof(f40,plain,(
% 23.44/3.49    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 23.44/3.49    inference(ennf_transformation,[],[f17])).
% 23.44/3.49  
% 23.44/3.49  fof(f41,plain,(
% 23.44/3.49    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 23.44/3.49    inference(flattening,[],[f40])).
% 23.44/3.49  
% 23.44/3.49  fof(f99,plain,(
% 23.44/3.49    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 23.44/3.49    inference(cnf_transformation,[],[f41])).
% 23.44/3.49  
% 23.44/3.49  fof(f112,plain,(
% 23.44/3.49    v1_funct_1(sK8)),
% 23.44/3.49    inference(cnf_transformation,[],[f67])).
% 23.44/3.49  
% 23.44/3.49  fof(f13,axiom,(
% 23.44/3.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 23.44/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.49  
% 23.44/3.49  fof(f35,plain,(
% 23.44/3.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.44/3.49    inference(ennf_transformation,[],[f13])).
% 23.44/3.49  
% 23.44/3.49  fof(f90,plain,(
% 23.44/3.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.44/3.49    inference(cnf_transformation,[],[f35])).
% 23.44/3.49  
% 23.44/3.49  fof(f1,axiom,(
% 23.44/3.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 23.44/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.49  
% 23.44/3.49  fof(f50,plain,(
% 23.44/3.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 23.44/3.49    inference(nnf_transformation,[],[f1])).
% 23.44/3.49  
% 23.44/3.49  fof(f51,plain,(
% 23.44/3.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 23.44/3.49    inference(rectify,[],[f50])).
% 23.44/3.49  
% 23.44/3.49  fof(f52,plain,(
% 23.44/3.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 23.44/3.49    introduced(choice_axiom,[])).
% 23.44/3.49  
% 23.44/3.49  fof(f53,plain,(
% 23.44/3.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 23.44/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f51,f52])).
% 23.44/3.49  
% 23.44/3.49  fof(f69,plain,(
% 23.44/3.49    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 23.44/3.49    inference(cnf_transformation,[],[f53])).
% 23.44/3.49  
% 23.44/3.49  fof(f8,axiom,(
% 23.44/3.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 23.44/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.49  
% 23.44/3.49  fof(f28,plain,(
% 23.44/3.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 23.44/3.49    inference(ennf_transformation,[],[f8])).
% 23.44/3.49  
% 23.44/3.49  fof(f55,plain,(
% 23.44/3.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 23.44/3.49    inference(nnf_transformation,[],[f28])).
% 23.44/3.49  
% 23.44/3.49  fof(f77,plain,(
% 23.44/3.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 23.44/3.49    inference(cnf_transformation,[],[f55])).
% 23.44/3.49  
% 23.44/3.49  fof(f7,axiom,(
% 23.44/3.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 23.44/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.49  
% 23.44/3.49  fof(f27,plain,(
% 23.44/3.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 23.44/3.49    inference(ennf_transformation,[],[f7])).
% 23.44/3.49  
% 23.44/3.49  fof(f76,plain,(
% 23.44/3.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 23.44/3.49    inference(cnf_transformation,[],[f27])).
% 23.44/3.49  
% 23.44/3.49  fof(f6,axiom,(
% 23.44/3.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 23.44/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.49  
% 23.44/3.49  fof(f54,plain,(
% 23.44/3.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 23.44/3.49    inference(nnf_transformation,[],[f6])).
% 23.44/3.49  
% 23.44/3.49  fof(f75,plain,(
% 23.44/3.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 23.44/3.49    inference(cnf_transformation,[],[f54])).
% 23.44/3.49  
% 23.44/3.49  fof(f16,axiom,(
% 23.44/3.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 23.44/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.49  
% 23.44/3.49  fof(f38,plain,(
% 23.44/3.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.44/3.49    inference(ennf_transformation,[],[f16])).
% 23.44/3.49  
% 23.44/3.49  fof(f39,plain,(
% 23.44/3.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.44/3.49    inference(flattening,[],[f38])).
% 23.44/3.49  
% 23.44/3.49  fof(f62,plain,(
% 23.44/3.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.44/3.49    inference(nnf_transformation,[],[f39])).
% 23.44/3.49  
% 23.44/3.49  fof(f93,plain,(
% 23.44/3.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.44/3.49    inference(cnf_transformation,[],[f62])).
% 23.44/3.49  
% 23.44/3.49  fof(f11,axiom,(
% 23.44/3.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 23.44/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.49  
% 23.44/3.49  fof(f32,plain,(
% 23.44/3.49    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 23.44/3.49    inference(ennf_transformation,[],[f11])).
% 23.44/3.49  
% 23.44/3.49  fof(f33,plain,(
% 23.44/3.49    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 23.44/3.49    inference(flattening,[],[f32])).
% 23.44/3.49  
% 23.44/3.49  fof(f88,plain,(
% 23.44/3.49    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 23.44/3.49    inference(cnf_transformation,[],[f33])).
% 23.44/3.49  
% 23.44/3.49  fof(f68,plain,(
% 23.44/3.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 23.44/3.49    inference(cnf_transformation,[],[f53])).
% 23.44/3.49  
% 23.44/3.49  fof(f18,axiom,(
% 23.44/3.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 23.44/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.49  
% 23.44/3.49  fof(f42,plain,(
% 23.44/3.49    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 23.44/3.49    inference(ennf_transformation,[],[f18])).
% 23.44/3.49  
% 23.44/3.49  fof(f43,plain,(
% 23.44/3.49    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 23.44/3.49    inference(flattening,[],[f42])).
% 23.44/3.49  
% 23.44/3.49  fof(f100,plain,(
% 23.44/3.49    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 23.44/3.49    inference(cnf_transformation,[],[f43])).
% 23.44/3.49  
% 23.44/3.49  fof(f117,plain,(
% 23.44/3.49    k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9))),
% 23.44/3.49    inference(cnf_transformation,[],[f67])).
% 23.44/3.49  
% 23.44/3.49  cnf(c_44,negated_conjecture,
% 23.44/3.49      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
% 23.44/3.49      inference(cnf_transformation,[],[f113]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5041,plain,
% 23.44/3.49      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_23,plain,
% 23.44/3.49      ( v5_relat_1(X0,X1)
% 23.44/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 23.44/3.49      inference(cnf_transformation,[],[f91]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5057,plain,
% 23.44/3.49      ( v5_relat_1(X0,X1) = iProver_top
% 23.44/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_6896,plain,
% 23.44/3.49      ( v5_relat_1(sK8,sK4) = iProver_top ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_5041,c_5057]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_43,negated_conjecture,
% 23.44/3.49      ( m1_subset_1(sK9,sK5) ),
% 23.44/3.49      inference(cnf_transformation,[],[f114]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5042,plain,
% 23.44/3.49      ( m1_subset_1(sK9,sK5) = iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5,plain,
% 23.44/3.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 23.44/3.49      inference(cnf_transformation,[],[f73]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5074,plain,
% 23.44/3.49      ( m1_subset_1(X0,X1) != iProver_top
% 23.44/3.49      | r2_hidden(X0,X1) = iProver_top
% 23.44/3.49      | v1_xboole_0(X1) = iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_7026,plain,
% 23.44/3.49      ( r2_hidden(sK9,sK5) = iProver_top
% 23.44/3.49      | v1_xboole_0(sK5) = iProver_top ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_5042,c_5074]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_56,plain,
% 23.44/3.49      ( m1_subset_1(sK9,sK5) = iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_41,negated_conjecture,
% 23.44/3.49      ( k1_xboole_0 != sK5 ),
% 23.44/3.49      inference(cnf_transformation,[],[f116]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_3,plain,
% 23.44/3.49      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 23.44/3.49      inference(cnf_transformation,[],[f71]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5137,plain,
% 23.44/3.49      ( ~ v1_xboole_0(sK5) | k1_xboole_0 = sK5 ),
% 23.44/3.49      inference(instantiation,[status(thm)],[c_3]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5138,plain,
% 23.44/3.49      ( k1_xboole_0 = sK5 | v1_xboole_0(sK5) != iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_5137]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5202,plain,
% 23.44/3.49      ( ~ m1_subset_1(X0,sK5) | r2_hidden(X0,sK5) | v1_xboole_0(sK5) ),
% 23.44/3.49      inference(instantiation,[status(thm)],[c_5]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5456,plain,
% 23.44/3.49      ( ~ m1_subset_1(sK9,sK5) | r2_hidden(sK9,sK5) | v1_xboole_0(sK5) ),
% 23.44/3.49      inference(instantiation,[status(thm)],[c_5202]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5457,plain,
% 23.44/3.49      ( m1_subset_1(sK9,sK5) != iProver_top
% 23.44/3.49      | r2_hidden(sK9,sK5) = iProver_top
% 23.44/3.49      | v1_xboole_0(sK5) = iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_5456]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_7335,plain,
% 23.44/3.49      ( r2_hidden(sK9,sK5) = iProver_top ),
% 23.44/3.49      inference(global_propositional_subsumption,
% 23.44/3.49                [status(thm)],
% 23.44/3.49                [c_7026,c_56,c_41,c_5138,c_5457]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_24,plain,
% 23.44/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.44/3.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 23.44/3.49      inference(cnf_transformation,[],[f92]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5056,plain,
% 23.44/3.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 23.44/3.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_6905,plain,
% 23.44/3.49      ( k1_relset_1(sK6,sK4,sK8) = k1_relat_1(sK8) ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_5041,c_5056]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_42,negated_conjecture,
% 23.44/3.49      ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) ),
% 23.44/3.49      inference(cnf_transformation,[],[f115]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5043,plain,
% 23.44/3.49      ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) = iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_7204,plain,
% 23.44/3.49      ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relat_1(sK8)) = iProver_top ),
% 23.44/3.49      inference(demodulation,[status(thm)],[c_6905,c_5043]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_46,negated_conjecture,
% 23.44/3.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 23.44/3.49      inference(cnf_transformation,[],[f111]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5039,plain,
% 23.44/3.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_35,plain,
% 23.44/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 23.44/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.44/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 23.44/3.49      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 23.44/3.49      | ~ v1_funct_1(X0)
% 23.44/3.49      | k1_xboole_0 = X2 ),
% 23.44/3.49      inference(cnf_transformation,[],[f106]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5046,plain,
% 23.44/3.49      ( k1_xboole_0 = X0
% 23.44/3.49      | v1_funct_2(X1,X2,X0) != iProver_top
% 23.44/3.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 23.44/3.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 23.44/3.49      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 23.44/3.49      | v1_funct_1(X1) != iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_8666,plain,
% 23.44/3.49      ( sK6 = k1_xboole_0
% 23.44/3.49      | v1_funct_2(sK7,sK5,sK6) != iProver_top
% 23.44/3.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) = iProver_top
% 23.44/3.49      | r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top
% 23.44/3.49      | v1_funct_1(sK7) != iProver_top ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_5039,c_5046]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_48,negated_conjecture,
% 23.44/3.49      ( v1_funct_1(sK7) ),
% 23.44/3.49      inference(cnf_transformation,[],[f109]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_51,plain,
% 23.44/3.49      ( v1_funct_1(sK7) = iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_47,negated_conjecture,
% 23.44/3.49      ( v1_funct_2(sK7,sK5,sK6) ),
% 23.44/3.49      inference(cnf_transformation,[],[f110]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_52,plain,
% 23.44/3.49      ( v1_funct_2(sK7,sK5,sK6) = iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_2,plain,
% 23.44/3.49      ( v1_xboole_0(k1_xboole_0) ),
% 23.44/3.49      inference(cnf_transformation,[],[f70]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_49,negated_conjecture,
% 23.44/3.49      ( ~ v1_xboole_0(sK6) ),
% 23.44/3.49      inference(cnf_transformation,[],[f108]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_1253,plain,
% 23.44/3.49      ( sK6 != k1_xboole_0 ),
% 23.44/3.49      inference(resolution_lifted,[status(thm)],[c_2,c_49]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_9287,plain,
% 23.44/3.49      ( r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top
% 23.44/3.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) = iProver_top ),
% 23.44/3.49      inference(global_propositional_subsumption,
% 23.44/3.49                [status(thm)],
% 23.44/3.49                [c_8666,c_51,c_52,c_1253]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_9288,plain,
% 23.44/3.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) = iProver_top
% 23.44/3.49      | r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top ),
% 23.44/3.49      inference(renaming,[status(thm)],[c_9287]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_9293,plain,
% 23.44/3.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK8)))) = iProver_top ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_7204,c_9288]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_33,plain,
% 23.44/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 23.44/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.44/3.49      | ~ r2_hidden(X3,X1)
% 23.44/3.49      | r2_hidden(k1_funct_1(X0,X3),X2)
% 23.44/3.49      | ~ v1_funct_1(X0)
% 23.44/3.49      | k1_xboole_0 = X2 ),
% 23.44/3.49      inference(cnf_transformation,[],[f101]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5048,plain,
% 23.44/3.49      ( k1_xboole_0 = X0
% 23.44/3.49      | v1_funct_2(X1,X2,X0) != iProver_top
% 23.44/3.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 23.44/3.49      | r2_hidden(X3,X2) != iProver_top
% 23.44/3.49      | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
% 23.44/3.49      | v1_funct_1(X1) != iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_10367,plain,
% 23.44/3.49      ( k1_relat_1(sK8) = k1_xboole_0
% 23.44/3.49      | v1_funct_2(sK7,sK5,k1_relat_1(sK8)) != iProver_top
% 23.44/3.49      | r2_hidden(X0,sK5) != iProver_top
% 23.44/3.49      | r2_hidden(k1_funct_1(sK7,X0),k1_relat_1(sK8)) = iProver_top
% 23.44/3.49      | v1_funct_1(sK7) != iProver_top ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_9293,c_5048]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_37,plain,
% 23.44/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 23.44/3.49      | v1_funct_2(X0,X1,X3)
% 23.44/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.44/3.49      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 23.44/3.49      | ~ v1_funct_1(X0)
% 23.44/3.49      | k1_xboole_0 = X2 ),
% 23.44/3.49      inference(cnf_transformation,[],[f104]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5044,plain,
% 23.44/3.49      ( k1_xboole_0 = X0
% 23.44/3.49      | v1_funct_2(X1,X2,X0) != iProver_top
% 23.44/3.49      | v1_funct_2(X1,X2,X3) = iProver_top
% 23.44/3.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 23.44/3.49      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 23.44/3.49      | v1_funct_1(X1) != iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_6838,plain,
% 23.44/3.49      ( sK6 = k1_xboole_0
% 23.44/3.49      | v1_funct_2(sK7,sK5,X0) = iProver_top
% 23.44/3.49      | v1_funct_2(sK7,sK5,sK6) != iProver_top
% 23.44/3.49      | r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top
% 23.44/3.49      | v1_funct_1(sK7) != iProver_top ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_5039,c_5044]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_8455,plain,
% 23.44/3.49      ( r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top
% 23.44/3.49      | v1_funct_2(sK7,sK5,X0) = iProver_top ),
% 23.44/3.49      inference(global_propositional_subsumption,
% 23.44/3.49                [status(thm)],
% 23.44/3.49                [c_6838,c_51,c_52,c_1253]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_8456,plain,
% 23.44/3.49      ( v1_funct_2(sK7,sK5,X0) = iProver_top
% 23.44/3.49      | r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top ),
% 23.44/3.49      inference(renaming,[status(thm)],[c_8455]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_8461,plain,
% 23.44/3.49      ( v1_funct_2(sK7,sK5,k1_relat_1(sK8)) = iProver_top ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_7204,c_8456]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_14496,plain,
% 23.44/3.49      ( r2_hidden(k1_funct_1(sK7,X0),k1_relat_1(sK8)) = iProver_top
% 23.44/3.49      | r2_hidden(X0,sK5) != iProver_top
% 23.44/3.49      | k1_relat_1(sK8) = k1_xboole_0 ),
% 23.44/3.49      inference(global_propositional_subsumption,
% 23.44/3.49                [status(thm)],
% 23.44/3.49                [c_10367,c_51,c_8461]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_14497,plain,
% 23.44/3.49      ( k1_relat_1(sK8) = k1_xboole_0
% 23.44/3.49      | r2_hidden(X0,sK5) != iProver_top
% 23.44/3.49      | r2_hidden(k1_funct_1(sK7,X0),k1_relat_1(sK8)) = iProver_top ),
% 23.44/3.49      inference(renaming,[status(thm)],[c_14496]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_31,plain,
% 23.44/3.49      ( ~ v5_relat_1(X0,X1)
% 23.44/3.49      | ~ r2_hidden(X2,k1_relat_1(X0))
% 23.44/3.49      | ~ v1_funct_1(X0)
% 23.44/3.49      | ~ v1_relat_1(X0)
% 23.44/3.49      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 23.44/3.49      inference(cnf_transformation,[],[f99]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5050,plain,
% 23.44/3.49      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 23.44/3.49      | v5_relat_1(X1,X0) != iProver_top
% 23.44/3.49      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 23.44/3.49      | v1_funct_1(X1) != iProver_top
% 23.44/3.49      | v1_relat_1(X1) != iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_14504,plain,
% 23.44/3.49      ( k7_partfun1(X0,sK8,k1_funct_1(sK7,X1)) = k1_funct_1(sK8,k1_funct_1(sK7,X1))
% 23.44/3.49      | k1_relat_1(sK8) = k1_xboole_0
% 23.44/3.49      | v5_relat_1(sK8,X0) != iProver_top
% 23.44/3.49      | r2_hidden(X1,sK5) != iProver_top
% 23.44/3.49      | v1_funct_1(sK8) != iProver_top
% 23.44/3.49      | v1_relat_1(sK8) != iProver_top ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_14497,c_5050]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_45,negated_conjecture,
% 23.44/3.49      ( v1_funct_1(sK8) ),
% 23.44/3.49      inference(cnf_transformation,[],[f112]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_54,plain,
% 23.44/3.49      ( v1_funct_1(sK8) = iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_157,plain,
% 23.44/3.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_22,plain,
% 23.44/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.44/3.49      | v1_relat_1(X0) ),
% 23.44/3.49      inference(cnf_transformation,[],[f90]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5058,plain,
% 23.44/3.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.44/3.49      | v1_relat_1(X0) = iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_6443,plain,
% 23.44/3.49      ( v1_relat_1(sK8) = iProver_top ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_5041,c_5058]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_6444,plain,
% 23.44/3.49      ( v1_relat_1(sK7) = iProver_top ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_5039,c_5058]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_4065,plain,
% 23.44/3.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 23.44/3.49      theory(equality) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_12852,plain,
% 23.44/3.49      ( ~ v1_xboole_0(X0)
% 23.44/3.49      | v1_xboole_0(k1_relat_1(sK8))
% 23.44/3.49      | k1_relat_1(sK8) != X0 ),
% 23.44/3.49      inference(instantiation,[status(thm)],[c_4065]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_12858,plain,
% 23.44/3.49      ( k1_relat_1(sK8) != X0
% 23.44/3.49      | v1_xboole_0(X0) != iProver_top
% 23.44/3.49      | v1_xboole_0(k1_relat_1(sK8)) = iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_12852]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_12860,plain,
% 23.44/3.49      ( k1_relat_1(sK8) != k1_xboole_0
% 23.44/3.49      | v1_xboole_0(k1_relat_1(sK8)) = iProver_top
% 23.44/3.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 23.44/3.49      inference(instantiation,[status(thm)],[c_12858]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_9418,plain,
% 23.44/3.49      ( v5_relat_1(sK7,k1_relat_1(sK8)) = iProver_top ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_9293,c_5057]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_0,plain,
% 23.44/3.49      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 23.44/3.49      inference(cnf_transformation,[],[f69]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5079,plain,
% 23.44/3.49      ( r2_hidden(sK0(X0),X0) = iProver_top
% 23.44/3.49      | v1_xboole_0(X0) = iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_10,plain,
% 23.44/3.49      ( ~ v5_relat_1(X0,X1)
% 23.44/3.49      | r1_tarski(k2_relat_1(X0),X1)
% 23.44/3.49      | ~ v1_relat_1(X0) ),
% 23.44/3.49      inference(cnf_transformation,[],[f77]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5070,plain,
% 23.44/3.49      ( v5_relat_1(X0,X1) != iProver_top
% 23.44/3.49      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 23.44/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_8,plain,
% 23.44/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.44/3.49      | ~ r2_hidden(X2,X0)
% 23.44/3.49      | ~ v1_xboole_0(X1) ),
% 23.44/3.49      inference(cnf_transformation,[],[f76]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_6,plain,
% 23.44/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.44/3.49      inference(cnf_transformation,[],[f75]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_362,plain,
% 23.44/3.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 23.44/3.49      inference(prop_impl,[status(thm)],[c_6]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_363,plain,
% 23.44/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.44/3.49      inference(renaming,[status(thm)],[c_362]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_455,plain,
% 23.44/3.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 23.44/3.49      inference(bin_hyper_res,[status(thm)],[c_8,c_363]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5035,plain,
% 23.44/3.49      ( r1_tarski(X0,X1) != iProver_top
% 23.44/3.49      | r2_hidden(X2,X0) != iProver_top
% 23.44/3.49      | v1_xboole_0(X1) != iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_7036,plain,
% 23.44/3.49      ( v5_relat_1(X0,X1) != iProver_top
% 23.44/3.49      | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
% 23.44/3.49      | v1_relat_1(X0) != iProver_top
% 23.44/3.49      | v1_xboole_0(X1) != iProver_top ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_5070,c_5035]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_14833,plain,
% 23.44/3.49      ( v5_relat_1(X0,X1) != iProver_top
% 23.44/3.49      | v1_relat_1(X0) != iProver_top
% 23.44/3.49      | v1_xboole_0(X1) != iProver_top
% 23.44/3.49      | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_5079,c_7036]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_18491,plain,
% 23.44/3.49      ( v1_relat_1(sK7) != iProver_top
% 23.44/3.49      | v1_xboole_0(k1_relat_1(sK8)) != iProver_top
% 23.44/3.49      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_9418,c_14833]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_30,plain,
% 23.44/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 23.44/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.44/3.49      | k1_relset_1(X1,X2,X0) = X1
% 23.44/3.49      | k1_xboole_0 = X2 ),
% 23.44/3.49      inference(cnf_transformation,[],[f93]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5051,plain,
% 23.44/3.49      ( k1_relset_1(X0,X1,X2) = X0
% 23.44/3.49      | k1_xboole_0 = X1
% 23.44/3.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 23.44/3.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_8773,plain,
% 23.44/3.49      ( k1_relset_1(sK5,sK6,sK7) = sK5
% 23.44/3.49      | sK6 = k1_xboole_0
% 23.44/3.49      | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_5039,c_5051]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_6906,plain,
% 23.44/3.49      ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_5039,c_5056]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_8774,plain,
% 23.44/3.49      ( k1_relat_1(sK7) = sK5
% 23.44/3.49      | sK6 = k1_xboole_0
% 23.44/3.49      | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
% 23.44/3.49      inference(demodulation,[status(thm)],[c_8773,c_6906]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_9435,plain,
% 23.44/3.49      ( k1_relat_1(sK7) = sK5 ),
% 23.44/3.49      inference(global_propositional_subsumption,
% 23.44/3.49                [status(thm)],
% 23.44/3.49                [c_8774,c_52,c_1253]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_20,plain,
% 23.44/3.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 23.44/3.49      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 23.44/3.49      | ~ v1_funct_1(X1)
% 23.44/3.49      | ~ v1_relat_1(X1) ),
% 23.44/3.49      inference(cnf_transformation,[],[f88]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5060,plain,
% 23.44/3.49      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 23.44/3.49      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 23.44/3.49      | v1_funct_1(X1) != iProver_top
% 23.44/3.49      | v1_relat_1(X1) != iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_1,plain,
% 23.44/3.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 23.44/3.49      inference(cnf_transformation,[],[f68]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5078,plain,
% 23.44/3.49      ( r2_hidden(X0,X1) != iProver_top
% 23.44/3.49      | v1_xboole_0(X1) != iProver_top ),
% 23.44/3.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_8933,plain,
% 23.44/3.49      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 23.44/3.49      | v1_funct_1(X1) != iProver_top
% 23.44/3.49      | v1_relat_1(X1) != iProver_top
% 23.44/3.49      | v1_xboole_0(k2_relat_1(X1)) != iProver_top ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_5060,c_5078]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_18523,plain,
% 23.44/3.49      ( r2_hidden(X0,sK5) != iProver_top
% 23.44/3.49      | v1_funct_1(sK7) != iProver_top
% 23.44/3.49      | v1_relat_1(sK7) != iProver_top
% 23.44/3.49      | v1_xboole_0(k2_relat_1(sK7)) != iProver_top ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_9435,c_8933]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_19469,plain,
% 23.44/3.49      ( r2_hidden(X0,sK5) != iProver_top
% 23.44/3.49      | v1_xboole_0(k2_relat_1(sK7)) != iProver_top ),
% 23.44/3.49      inference(global_propositional_subsumption,
% 23.44/3.49                [status(thm)],
% 23.44/3.49                [c_18523,c_51,c_6444]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_19481,plain,
% 23.44/3.49      ( v1_xboole_0(k2_relat_1(sK7)) != iProver_top ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_7335,c_19469]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_75905,plain,
% 23.44/3.49      ( k7_partfun1(X0,sK8,k1_funct_1(sK7,X1)) = k1_funct_1(sK8,k1_funct_1(sK7,X1))
% 23.44/3.49      | v5_relat_1(sK8,X0) != iProver_top
% 23.44/3.49      | r2_hidden(X1,sK5) != iProver_top ),
% 23.44/3.49      inference(global_propositional_subsumption,
% 23.44/3.49                [status(thm)],
% 23.44/3.49                [c_14504,c_54,c_157,c_6443,c_6444,c_12860,c_18491,
% 23.44/3.49                 c_19481]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_75921,plain,
% 23.44/3.49      ( k7_partfun1(X0,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9))
% 23.44/3.49      | v5_relat_1(sK8,X0) != iProver_top ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_7335,c_75905]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_76028,plain,
% 23.44/3.49      ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
% 23.44/3.49      inference(superposition,[status(thm)],[c_6896,c_75921]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_32,plain,
% 23.44/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 23.44/3.49      | ~ m1_subset_1(X3,X1)
% 23.44/3.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 23.44/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.44/3.49      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 23.44/3.49      | ~ v1_funct_1(X4)
% 23.44/3.49      | ~ v1_funct_1(X0)
% 23.44/3.49      | v1_xboole_0(X2)
% 23.44/3.49      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 23.44/3.49      | k1_xboole_0 = X1 ),
% 23.44/3.49      inference(cnf_transformation,[],[f100]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5195,plain,
% 23.44/3.49      ( ~ v1_funct_2(X0,X1,sK6)
% 23.44/3.49      | ~ m1_subset_1(X2,X1)
% 23.44/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK6)))
% 23.44/3.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,X4)))
% 23.44/3.49      | ~ r1_tarski(k2_relset_1(X1,sK6,X0),k1_relset_1(sK6,X4,X3))
% 23.44/3.49      | ~ v1_funct_1(X0)
% 23.44/3.49      | ~ v1_funct_1(X3)
% 23.44/3.49      | v1_xboole_0(sK6)
% 23.44/3.49      | k1_funct_1(k8_funct_2(X1,sK6,X4,X0,X3),X2) = k1_funct_1(X3,k1_funct_1(X0,X2))
% 23.44/3.49      | k1_xboole_0 = X1 ),
% 23.44/3.49      inference(instantiation,[status(thm)],[c_32]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5401,plain,
% 23.44/3.49      ( ~ v1_funct_2(X0,sK5,sK6)
% 23.44/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X2)))
% 23.44/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 23.44/3.49      | ~ m1_subset_1(X3,sK5)
% 23.44/3.49      | ~ r1_tarski(k2_relset_1(sK5,sK6,X0),k1_relset_1(sK6,X2,X1))
% 23.44/3.49      | ~ v1_funct_1(X0)
% 23.44/3.49      | ~ v1_funct_1(X1)
% 23.44/3.49      | v1_xboole_0(sK6)
% 23.44/3.49      | k1_funct_1(k8_funct_2(sK5,sK6,X2,X0,X1),X3) = k1_funct_1(X1,k1_funct_1(X0,X3))
% 23.44/3.49      | k1_xboole_0 = sK5 ),
% 23.44/3.49      inference(instantiation,[status(thm)],[c_5195]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5748,plain,
% 23.44/3.49      ( ~ v1_funct_2(X0,sK5,sK6)
% 23.44/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X2)))
% 23.44/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 23.44/3.49      | ~ m1_subset_1(sK9,sK5)
% 23.44/3.49      | ~ r1_tarski(k2_relset_1(sK5,sK6,X0),k1_relset_1(sK6,X2,X1))
% 23.44/3.49      | ~ v1_funct_1(X0)
% 23.44/3.49      | ~ v1_funct_1(X1)
% 23.44/3.49      | v1_xboole_0(sK6)
% 23.44/3.49      | k1_funct_1(k8_funct_2(sK5,sK6,X2,X0,X1),sK9) = k1_funct_1(X1,k1_funct_1(X0,sK9))
% 23.44/3.49      | k1_xboole_0 = sK5 ),
% 23.44/3.49      inference(instantiation,[status(thm)],[c_5401]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_6322,plain,
% 23.44/3.49      ( ~ v1_funct_2(sK7,sK5,sK6)
% 23.44/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,X1)))
% 23.44/3.49      | ~ m1_subset_1(sK9,sK5)
% 23.44/3.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 23.44/3.49      | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,X1,X0))
% 23.44/3.49      | ~ v1_funct_1(X0)
% 23.44/3.49      | ~ v1_funct_1(sK7)
% 23.44/3.49      | v1_xboole_0(sK6)
% 23.44/3.49      | k1_funct_1(k8_funct_2(sK5,sK6,X1,sK7,X0),sK9) = k1_funct_1(X0,k1_funct_1(sK7,sK9))
% 23.44/3.49      | k1_xboole_0 = sK5 ),
% 23.44/3.49      inference(instantiation,[status(thm)],[c_5748]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_7455,plain,
% 23.44/3.49      ( ~ v1_funct_2(sK7,sK5,sK6)
% 23.44/3.49      | ~ m1_subset_1(sK9,sK5)
% 23.44/3.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
% 23.44/3.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 23.44/3.49      | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
% 23.44/3.49      | ~ v1_funct_1(sK8)
% 23.44/3.49      | ~ v1_funct_1(sK7)
% 23.44/3.49      | v1_xboole_0(sK6)
% 23.44/3.49      | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) = k1_funct_1(sK8,k1_funct_1(sK7,sK9))
% 23.44/3.49      | k1_xboole_0 = sK5 ),
% 23.44/3.49      inference(instantiation,[status(thm)],[c_6322]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_4064,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5134,plain,
% 23.44/3.49      ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != X0
% 23.44/3.49      | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != X0
% 23.44/3.49      | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) = k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) ),
% 23.44/3.49      inference(instantiation,[status(thm)],[c_4064]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_5233,plain,
% 23.44/3.49      ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
% 23.44/3.49      | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) = k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9))
% 23.44/3.49      | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
% 23.44/3.49      inference(instantiation,[status(thm)],[c_5134]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(c_40,negated_conjecture,
% 23.44/3.49      ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) ),
% 23.44/3.49      inference(cnf_transformation,[],[f117]) ).
% 23.44/3.49  
% 23.44/3.49  cnf(contradiction,plain,
% 23.44/3.49      ( $false ),
% 23.44/3.49      inference(minisat,
% 23.44/3.49                [status(thm)],
% 23.44/3.49                [c_76028,c_7455,c_5233,c_40,c_41,c_42,c_43,c_44,c_45,
% 23.44/3.49                 c_46,c_47,c_48,c_49]) ).
% 23.44/3.49  
% 23.44/3.49  
% 23.44/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.44/3.49  
% 23.44/3.49  ------                               Statistics
% 23.44/3.49  
% 23.44/3.49  ------ General
% 23.44/3.49  
% 23.44/3.49  abstr_ref_over_cycles:                  0
% 23.44/3.49  abstr_ref_under_cycles:                 0
% 23.44/3.49  gc_basic_clause_elim:                   0
% 23.44/3.49  forced_gc_time:                         0
% 23.44/3.49  parsing_time:                           0.017
% 23.44/3.49  unif_index_cands_time:                  0.
% 23.44/3.49  unif_index_add_time:                    0.
% 23.44/3.49  orderings_time:                         0.
% 23.44/3.49  out_proof_time:                         0.021
% 23.44/3.49  total_time:                             2.654
% 23.44/3.49  num_of_symbols:                         60
% 23.44/3.49  num_of_terms:                           86571
% 23.44/3.49  
% 23.44/3.49  ------ Preprocessing
% 23.44/3.49  
% 23.44/3.49  num_of_splits:                          0
% 23.44/3.49  num_of_split_atoms:                     0
% 23.44/3.49  num_of_reused_defs:                     0
% 23.44/3.49  num_eq_ax_congr_red:                    51
% 23.44/3.49  num_of_sem_filtered_clauses:            1
% 23.44/3.49  num_of_subtypes:                        0
% 23.44/3.49  monotx_restored_types:                  0
% 23.44/3.49  sat_num_of_epr_types:                   0
% 23.44/3.49  sat_num_of_non_cyclic_types:            0
% 23.44/3.49  sat_guarded_non_collapsed_types:        0
% 23.44/3.49  num_pure_diseq_elim:                    0
% 23.44/3.49  simp_replaced_by:                       0
% 23.44/3.49  res_preprocessed:                       223
% 23.44/3.49  prep_upred:                             0
% 23.44/3.49  prep_unflattend:                        134
% 23.44/3.49  smt_new_axioms:                         0
% 23.44/3.49  pred_elim_cands:                        8
% 23.44/3.49  pred_elim:                              0
% 23.44/3.49  pred_elim_cl:                           0
% 23.44/3.49  pred_elim_cycles:                       9
% 23.44/3.49  merged_defs:                            8
% 23.44/3.49  merged_defs_ncl:                        0
% 23.44/3.49  bin_hyper_res:                          9
% 23.44/3.49  prep_cycles:                            4
% 23.44/3.49  pred_elim_time:                         0.055
% 23.44/3.49  splitting_time:                         0.
% 23.44/3.49  sem_filter_time:                        0.
% 23.44/3.49  monotx_time:                            0.
% 23.44/3.49  subtype_inf_time:                       0.
% 23.44/3.49  
% 23.44/3.49  ------ Problem properties
% 23.44/3.49  
% 23.44/3.49  clauses:                                48
% 23.44/3.49  conjectures:                            10
% 23.44/3.49  epr:                                    15
% 23.44/3.49  horn:                                   35
% 23.44/3.49  ground:                                 11
% 23.44/3.49  unary:                                  12
% 23.44/3.49  binary:                                 11
% 23.44/3.49  lits:                                   150
% 23.44/3.49  lits_eq:                                26
% 23.44/3.49  fd_pure:                                0
% 23.44/3.49  fd_pseudo:                              0
% 23.44/3.49  fd_cond:                                8
% 23.44/3.49  fd_pseudo_cond:                         4
% 23.44/3.49  ac_symbols:                             0
% 23.44/3.49  
% 23.44/3.49  ------ Propositional Solver
% 23.44/3.49  
% 23.44/3.49  prop_solver_calls:                      41
% 23.44/3.49  prop_fast_solver_calls:                 4703
% 23.44/3.49  smt_solver_calls:                       0
% 23.44/3.49  smt_fast_solver_calls:                  0
% 23.44/3.49  prop_num_of_clauses:                    37615
% 23.44/3.49  prop_preprocess_simplified:             55297
% 23.44/3.49  prop_fo_subsumed:                       252
% 23.44/3.49  prop_solver_time:                       0.
% 23.44/3.49  smt_solver_time:                        0.
% 23.44/3.49  smt_fast_solver_time:                   0.
% 23.44/3.49  prop_fast_solver_time:                  0.
% 23.44/3.49  prop_unsat_core_time:                   0.004
% 23.44/3.49  
% 23.44/3.49  ------ QBF
% 23.44/3.49  
% 23.44/3.49  qbf_q_res:                              0
% 23.44/3.49  qbf_num_tautologies:                    0
% 23.44/3.49  qbf_prep_cycles:                        0
% 23.44/3.49  
% 23.44/3.49  ------ BMC1
% 23.44/3.49  
% 23.44/3.49  bmc1_current_bound:                     -1
% 23.44/3.49  bmc1_last_solved_bound:                 -1
% 23.44/3.49  bmc1_unsat_core_size:                   -1
% 23.44/3.49  bmc1_unsat_core_parents_size:           -1
% 23.44/3.49  bmc1_merge_next_fun:                    0
% 23.44/3.49  bmc1_unsat_core_clauses_time:           0.
% 23.44/3.49  
% 23.44/3.49  ------ Instantiation
% 23.44/3.49  
% 23.44/3.49  inst_num_of_clauses:                    41
% 23.44/3.49  inst_num_in_passive:                    3
% 23.44/3.49  inst_num_in_active:                     2514
% 23.44/3.49  inst_num_in_unprocessed:                19
% 23.44/3.49  inst_num_of_loops:                      3019
% 23.44/3.49  inst_num_of_learning_restarts:          1
% 23.44/3.49  inst_num_moves_active_passive:          502
% 23.44/3.49  inst_lit_activity:                      0
% 23.44/3.49  inst_lit_activity_moves:                0
% 23.44/3.49  inst_num_tautologies:                   0
% 23.44/3.49  inst_num_prop_implied:                  0
% 23.44/3.49  inst_num_existing_simplified:           0
% 23.44/3.49  inst_num_eq_res_simplified:             0
% 23.44/3.49  inst_num_child_elim:                    0
% 23.44/3.49  inst_num_of_dismatching_blockings:      5268
% 23.44/3.49  inst_num_of_non_proper_insts:           7706
% 23.44/3.49  inst_num_of_duplicates:                 0
% 23.44/3.49  inst_inst_num_from_inst_to_res:         0
% 23.44/3.49  inst_dismatching_checking_time:         0.
% 23.44/3.49  
% 23.44/3.49  ------ Resolution
% 23.44/3.49  
% 23.44/3.49  res_num_of_clauses:                     63
% 23.44/3.49  res_num_in_passive:                     63
% 23.44/3.49  res_num_in_active:                      0
% 23.44/3.49  res_num_of_loops:                       227
% 23.44/3.49  res_forward_subset_subsumed:            530
% 23.44/3.49  res_backward_subset_subsumed:           30
% 23.44/3.49  res_forward_subsumed:                   0
% 23.44/3.49  res_backward_subsumed:                  0
% 23.44/3.49  res_forward_subsumption_resolution:     0
% 23.44/3.49  res_backward_subsumption_resolution:    1
% 23.44/3.49  res_clause_to_clause_subsumption:       37882
% 23.44/3.49  res_orphan_elimination:                 0
% 23.44/3.49  res_tautology_del:                      360
% 23.44/3.49  res_num_eq_res_simplified:              0
% 23.44/3.49  res_num_sel_changes:                    0
% 23.44/3.49  res_moves_from_active_to_pass:          0
% 23.44/3.49  
% 23.44/3.49  ------ Superposition
% 23.44/3.49  
% 23.44/3.49  sup_time_total:                         0.
% 23.44/3.49  sup_time_generating:                    0.
% 23.44/3.49  sup_time_sim_full:                      0.
% 23.44/3.49  sup_time_sim_immed:                     0.
% 23.44/3.49  
% 23.44/3.49  sup_num_of_clauses:                     5009
% 23.44/3.49  sup_num_in_active:                      581
% 23.44/3.49  sup_num_in_passive:                     4428
% 23.44/3.49  sup_num_of_loops:                       603
% 23.44/3.49  sup_fw_superposition:                   3889
% 23.44/3.49  sup_bw_superposition:                   2180
% 23.44/3.49  sup_immediate_simplified:               962
% 23.44/3.49  sup_given_eliminated:                   3
% 23.44/3.49  comparisons_done:                       0
% 23.44/3.49  comparisons_avoided:                    237
% 23.44/3.49  
% 23.44/3.49  ------ Simplifications
% 23.44/3.49  
% 23.44/3.49  
% 23.44/3.49  sim_fw_subset_subsumed:                 504
% 23.44/3.49  sim_bw_subset_subsumed:                 2
% 23.44/3.49  sim_fw_subsumed:                        180
% 23.44/3.49  sim_bw_subsumed:                        45
% 23.44/3.49  sim_fw_subsumption_res:                 0
% 23.44/3.49  sim_bw_subsumption_res:                 0
% 23.44/3.49  sim_tautology_del:                      10
% 23.44/3.49  sim_eq_tautology_del:                   237
% 23.44/3.49  sim_eq_res_simp:                        0
% 23.44/3.49  sim_fw_demodulated:                     7
% 23.44/3.49  sim_bw_demodulated:                     5
% 23.44/3.49  sim_light_normalised:                   310
% 23.44/3.49  sim_joinable_taut:                      0
% 23.44/3.49  sim_joinable_simp:                      0
% 23.44/3.49  sim_ac_normalised:                      0
% 23.44/3.49  sim_smt_subsumption:                    0
% 23.44/3.49  
%------------------------------------------------------------------------------

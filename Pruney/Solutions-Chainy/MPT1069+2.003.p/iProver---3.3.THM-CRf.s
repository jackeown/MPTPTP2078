%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:42 EST 2020

% Result     : Theorem 7.25s
% Output     : CNFRefutation 7.25s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 789 expanded)
%              Number of clauses        :  129 ( 234 expanded)
%              Number of leaves         :   28 ( 258 expanded)
%              Depth                    :   20
%              Number of atoms          :  770 (5620 expanded)
%              Number of equality atoms :  307 (1515 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,conjecture,(
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

fof(f28,negated_conjecture,(
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
    inference(negated_conjecture,[],[f27])).

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f70,plain,(
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

fof(f69,plain,(
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

fof(f68,plain,(
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

fof(f67,plain,
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

fof(f71,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f59,f70,f69,f68,f67])).

fof(f117,plain,(
    m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f119,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f71])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f73,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f116,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f71])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f114,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f71])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f118,plain,(
    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f71])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f26,axiom,(
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

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f111,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f112,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f113,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f54])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f50])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f115,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f71])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f60])).

fof(f76,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f22,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f92,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v5_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f24,axiom,(
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

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f103,plain,(
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
    inference(cnf_transformation,[],[f53])).

fof(f120,plain,(
    k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2385,plain,
    ( m1_subset_1(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2411,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5516,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2385,c_2411])).

cnf(c_55,plain,
    ( m1_subset_1(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_40,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2746,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2747,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2746])).

cnf(c_2934,plain,
    ( r2_hidden(X0,sK2)
    | ~ m1_subset_1(X0,sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3252,plain,
    ( r2_hidden(sK6,sK2)
    | ~ m1_subset_1(sK6,sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2934])).

cnf(c_3253,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | m1_subset_1(sK6,sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3252])).

cnf(c_5806,plain,
    ( r2_hidden(sK6,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5516,c_55,c_40,c_2747,c_3253])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2384,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_23,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2397,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4316,plain,
    ( v5_relat_1(sK5,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2384,c_2397])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2382,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2394,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4342,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2382,c_2394])).

cnf(c_41,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2386,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_4893,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4342,c_2386])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2395,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5103,plain,
    ( k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2384,c_2395])).

cnf(c_5707,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4893,c_5103])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2389,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_6073,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2382,c_2389])).

cnf(c_6079,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6073,c_4342])).

cnf(c_48,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_47,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_50,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_51,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1435,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2796,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1435])).

cnf(c_2798,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2796])).

cnf(c_6961,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6079,c_48,c_50,c_51,c_0,c_2798])).

cnf(c_6962,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6961])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2391,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7611,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(sK4,sK2,X0) != iProver_top
    | r2_hidden(X1,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X1),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6962,c_2391])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2387,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4063,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,X0) = iProver_top
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2382,c_2387])).

cnf(c_6043,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top
    | v1_funct_2(sK4,sK2,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4063,c_48,c_50,c_51,c_0,c_2798])).

cnf(c_6044,plain,
    ( v1_funct_2(sK4,sK2,X0) = iProver_top
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6043])).

cnf(c_6049,plain,
    ( v1_funct_2(sK4,sK2,X0) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6044,c_4342])).

cnf(c_13072,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X1),X0) = iProver_top
    | r2_hidden(X1,sK2) != iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7611,c_50,c_6049])).

cnf(c_13073,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X1),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13072])).

cnf(c_30,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2393,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | v5_relat_1(X1,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_13081,plain,
    ( k7_partfun1(X0,X1,k1_funct_1(sK4,X2)) = k1_funct_1(X1,k1_funct_1(sK4,X2))
    | k1_relat_1(X1) = k1_xboole_0
    | v5_relat_1(X1,X0) != iProver_top
    | r2_hidden(X2,sK2) != iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_13073,c_2393])).

cnf(c_25426,plain,
    ( k7_partfun1(X0,sK5,k1_funct_1(sK4,X1)) = k1_funct_1(sK5,k1_funct_1(sK4,X1))
    | k1_relat_1(sK5) = k1_xboole_0
    | v5_relat_1(sK5,X0) != iProver_top
    | r2_hidden(X1,sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5707,c_13081])).

cnf(c_49,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_52,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_53,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_54,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_133,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_132,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_134,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_138,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_143,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2771,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2772,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2771])).

cnf(c_2774,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2775,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2774])).

cnf(c_16,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2990,plain,
    ( ~ v5_relat_1(sK4,X0)
    | r1_tarski(k2_relat_1(sK4),X0)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3006,plain,
    ( v5_relat_1(sK4,X0) != iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2990])).

cnf(c_3008,plain,
    ( v5_relat_1(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3006])).

cnf(c_1436,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3304,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK5),X2)
    | X2 != X1
    | k1_relat_1(sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_1436])).

cnf(c_3305,plain,
    ( X0 != X1
    | k1_relat_1(sK5) != X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k1_relat_1(sK5),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3304])).

cnf(c_3307,plain,
    ( k1_relat_1(sK5) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_relat_1(sK5),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3305])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_20,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_254,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_20])).

cnf(c_255,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(renaming,[status(thm)],[c_254])).

cnf(c_2378,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_255])).

cnf(c_3457,plain,
    ( v1_funct_2(sK4,sK2,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2382,c_2378])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3688,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_xboole_0(k2_relat_1(sK4))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3689,plain,
    ( v1_relat_1(sK4) != iProver_top
    | v1_xboole_0(k2_relat_1(sK4)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3688])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_340,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_341,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_340])).

cnf(c_414,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_341])).

cnf(c_5548,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_414])).

cnf(c_5552,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5548])).

cnf(c_5554,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
    | v1_xboole_0(k2_relat_1(sK4)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5552])).

cnf(c_15,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2405,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6228,plain,
    ( v5_relat_1(sK4,k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5707,c_2405])).

cnf(c_10700,plain,
    ( v5_relat_1(sK4,k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6228,c_52,c_2775])).

cnf(c_19,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(X0,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2401,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | v5_relat_1(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10705,plain,
    ( v5_relat_1(sK4,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK5),X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10700,c_2401])).

cnf(c_10707,plain,
    ( v5_relat_1(sK4,k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(sK5),k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10705])).

cnf(c_25462,plain,
    ( k7_partfun1(X0,sK5,k1_funct_1(sK4,X1)) = k1_funct_1(sK5,k1_funct_1(sK4,X1))
    | v5_relat_1(sK5,X0) != iProver_top
    | r2_hidden(X1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25426,c_49,c_51,c_52,c_53,c_54,c_40,c_133,c_134,c_138,c_143,c_2747,c_2772,c_2775,c_3008,c_3307,c_3457,c_3689,c_5554,c_10707])).

cnf(c_25471,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,X0)) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4316,c_25462])).

cnf(c_25619,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(superposition,[status(thm)],[c_5806,c_25471])).

cnf(c_31,plain,
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
    inference(cnf_transformation,[],[f103])).

cnf(c_2392,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8268,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))
    | sK2 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
    | m1_subset_1(X2,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4342,c_2392])).

cnf(c_1434,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2834,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1434])).

cnf(c_2835,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2834])).

cnf(c_9120,plain,
    ( m1_subset_1(X2,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
    | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))
    | r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8268,c_49,c_50,c_51,c_52,c_40,c_133,c_138,c_2835])).

cnf(c_9121,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
    | m1_subset_1(X2,sK2) != iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9120])).

cnf(c_9132,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5103,c_9121])).

cnf(c_9162,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9132,c_53,c_54,c_5707])).

cnf(c_9163,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_9162])).

cnf(c_9171,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(superposition,[status(thm)],[c_2385,c_9163])).

cnf(c_39,negated_conjecture,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_9968,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(demodulation,[status(thm)],[c_9171,c_39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25619,c_9968])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.25/1.61  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.25/1.61  
% 7.25/1.61  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.25/1.61  
% 7.25/1.61  ------  iProver source info
% 7.25/1.61  
% 7.25/1.61  git: date: 2020-06-30 10:37:57 +0100
% 7.25/1.61  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.25/1.61  git: non_committed_changes: false
% 7.25/1.61  git: last_make_outside_of_git: false
% 7.25/1.61  
% 7.25/1.61  ------ 
% 7.25/1.61  
% 7.25/1.61  ------ Input Options
% 7.25/1.61  
% 7.25/1.61  --out_options                           all
% 7.25/1.61  --tptp_safe_out                         true
% 7.25/1.61  --problem_path                          ""
% 7.25/1.61  --include_path                          ""
% 7.25/1.61  --clausifier                            res/vclausify_rel
% 7.25/1.61  --clausifier_options                    --mode clausify
% 7.25/1.61  --stdin                                 false
% 7.25/1.61  --stats_out                             all
% 7.25/1.61  
% 7.25/1.61  ------ General Options
% 7.25/1.61  
% 7.25/1.61  --fof                                   false
% 7.25/1.61  --time_out_real                         305.
% 7.25/1.61  --time_out_virtual                      -1.
% 7.25/1.61  --symbol_type_check                     false
% 7.25/1.61  --clausify_out                          false
% 7.25/1.61  --sig_cnt_out                           false
% 7.25/1.61  --trig_cnt_out                          false
% 7.25/1.61  --trig_cnt_out_tolerance                1.
% 7.25/1.61  --trig_cnt_out_sk_spl                   false
% 7.25/1.61  --abstr_cl_out                          false
% 7.25/1.61  
% 7.25/1.61  ------ Global Options
% 7.25/1.61  
% 7.25/1.61  --schedule                              default
% 7.25/1.61  --add_important_lit                     false
% 7.25/1.61  --prop_solver_per_cl                    1000
% 7.25/1.61  --min_unsat_core                        false
% 7.25/1.61  --soft_assumptions                      false
% 7.25/1.61  --soft_lemma_size                       3
% 7.25/1.61  --prop_impl_unit_size                   0
% 7.25/1.61  --prop_impl_unit                        []
% 7.25/1.61  --share_sel_clauses                     true
% 7.25/1.61  --reset_solvers                         false
% 7.25/1.61  --bc_imp_inh                            [conj_cone]
% 7.25/1.61  --conj_cone_tolerance                   3.
% 7.25/1.61  --extra_neg_conj                        none
% 7.25/1.61  --large_theory_mode                     true
% 7.25/1.61  --prolific_symb_bound                   200
% 7.25/1.61  --lt_threshold                          2000
% 7.25/1.61  --clause_weak_htbl                      true
% 7.25/1.61  --gc_record_bc_elim                     false
% 7.25/1.61  
% 7.25/1.61  ------ Preprocessing Options
% 7.25/1.61  
% 7.25/1.61  --preprocessing_flag                    true
% 7.25/1.61  --time_out_prep_mult                    0.1
% 7.25/1.61  --splitting_mode                        input
% 7.25/1.61  --splitting_grd                         true
% 7.25/1.61  --splitting_cvd                         false
% 7.25/1.61  --splitting_cvd_svl                     false
% 7.25/1.61  --splitting_nvd                         32
% 7.25/1.61  --sub_typing                            true
% 7.25/1.61  --prep_gs_sim                           true
% 7.25/1.61  --prep_unflatten                        true
% 7.25/1.61  --prep_res_sim                          true
% 7.25/1.61  --prep_upred                            true
% 7.25/1.61  --prep_sem_filter                       exhaustive
% 7.25/1.61  --prep_sem_filter_out                   false
% 7.25/1.61  --pred_elim                             true
% 7.25/1.61  --res_sim_input                         true
% 7.25/1.61  --eq_ax_congr_red                       true
% 7.25/1.61  --pure_diseq_elim                       true
% 7.25/1.61  --brand_transform                       false
% 7.25/1.61  --non_eq_to_eq                          false
% 7.25/1.61  --prep_def_merge                        true
% 7.25/1.61  --prep_def_merge_prop_impl              false
% 7.25/1.61  --prep_def_merge_mbd                    true
% 7.25/1.61  --prep_def_merge_tr_red                 false
% 7.25/1.61  --prep_def_merge_tr_cl                  false
% 7.25/1.61  --smt_preprocessing                     true
% 7.25/1.61  --smt_ac_axioms                         fast
% 7.25/1.61  --preprocessed_out                      false
% 7.25/1.61  --preprocessed_stats                    false
% 7.25/1.61  
% 7.25/1.61  ------ Abstraction refinement Options
% 7.25/1.61  
% 7.25/1.61  --abstr_ref                             []
% 7.25/1.61  --abstr_ref_prep                        false
% 7.25/1.61  --abstr_ref_until_sat                   false
% 7.25/1.61  --abstr_ref_sig_restrict                funpre
% 7.25/1.61  --abstr_ref_af_restrict_to_split_sk     false
% 7.25/1.61  --abstr_ref_under                       []
% 7.25/1.61  
% 7.25/1.61  ------ SAT Options
% 7.25/1.61  
% 7.25/1.61  --sat_mode                              false
% 7.25/1.61  --sat_fm_restart_options                ""
% 7.25/1.61  --sat_gr_def                            false
% 7.25/1.61  --sat_epr_types                         true
% 7.25/1.61  --sat_non_cyclic_types                  false
% 7.25/1.61  --sat_finite_models                     false
% 7.25/1.61  --sat_fm_lemmas                         false
% 7.25/1.61  --sat_fm_prep                           false
% 7.25/1.61  --sat_fm_uc_incr                        true
% 7.25/1.61  --sat_out_model                         small
% 7.25/1.61  --sat_out_clauses                       false
% 7.25/1.61  
% 7.25/1.61  ------ QBF Options
% 7.25/1.61  
% 7.25/1.61  --qbf_mode                              false
% 7.25/1.61  --qbf_elim_univ                         false
% 7.25/1.61  --qbf_dom_inst                          none
% 7.25/1.61  --qbf_dom_pre_inst                      false
% 7.25/1.61  --qbf_sk_in                             false
% 7.25/1.61  --qbf_pred_elim                         true
% 7.25/1.61  --qbf_split                             512
% 7.25/1.61  
% 7.25/1.61  ------ BMC1 Options
% 7.25/1.61  
% 7.25/1.61  --bmc1_incremental                      false
% 7.25/1.61  --bmc1_axioms                           reachable_all
% 7.25/1.61  --bmc1_min_bound                        0
% 7.25/1.61  --bmc1_max_bound                        -1
% 7.25/1.61  --bmc1_max_bound_default                -1
% 7.25/1.61  --bmc1_symbol_reachability              true
% 7.25/1.61  --bmc1_property_lemmas                  false
% 7.25/1.61  --bmc1_k_induction                      false
% 7.25/1.61  --bmc1_non_equiv_states                 false
% 7.25/1.61  --bmc1_deadlock                         false
% 7.25/1.61  --bmc1_ucm                              false
% 7.25/1.61  --bmc1_add_unsat_core                   none
% 7.25/1.61  --bmc1_unsat_core_children              false
% 7.25/1.61  --bmc1_unsat_core_extrapolate_axioms    false
% 7.25/1.61  --bmc1_out_stat                         full
% 7.25/1.61  --bmc1_ground_init                      false
% 7.25/1.61  --bmc1_pre_inst_next_state              false
% 7.25/1.61  --bmc1_pre_inst_state                   false
% 7.25/1.61  --bmc1_pre_inst_reach_state             false
% 7.25/1.61  --bmc1_out_unsat_core                   false
% 7.25/1.61  --bmc1_aig_witness_out                  false
% 7.25/1.61  --bmc1_verbose                          false
% 7.25/1.61  --bmc1_dump_clauses_tptp                false
% 7.25/1.61  --bmc1_dump_unsat_core_tptp             false
% 7.25/1.61  --bmc1_dump_file                        -
% 7.25/1.61  --bmc1_ucm_expand_uc_limit              128
% 7.25/1.61  --bmc1_ucm_n_expand_iterations          6
% 7.25/1.61  --bmc1_ucm_extend_mode                  1
% 7.25/1.61  --bmc1_ucm_init_mode                    2
% 7.25/1.61  --bmc1_ucm_cone_mode                    none
% 7.25/1.61  --bmc1_ucm_reduced_relation_type        0
% 7.25/1.61  --bmc1_ucm_relax_model                  4
% 7.25/1.61  --bmc1_ucm_full_tr_after_sat            true
% 7.25/1.61  --bmc1_ucm_expand_neg_assumptions       false
% 7.25/1.61  --bmc1_ucm_layered_model                none
% 7.25/1.61  --bmc1_ucm_max_lemma_size               10
% 7.25/1.61  
% 7.25/1.61  ------ AIG Options
% 7.25/1.61  
% 7.25/1.61  --aig_mode                              false
% 7.25/1.61  
% 7.25/1.61  ------ Instantiation Options
% 7.25/1.61  
% 7.25/1.61  --instantiation_flag                    true
% 7.25/1.61  --inst_sos_flag                         false
% 7.25/1.61  --inst_sos_phase                        true
% 7.25/1.61  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.25/1.61  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.25/1.61  --inst_lit_sel_side                     num_symb
% 7.25/1.61  --inst_solver_per_active                1400
% 7.25/1.61  --inst_solver_calls_frac                1.
% 7.25/1.61  --inst_passive_queue_type               priority_queues
% 7.25/1.61  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.25/1.61  --inst_passive_queues_freq              [25;2]
% 7.25/1.61  --inst_dismatching                      true
% 7.25/1.61  --inst_eager_unprocessed_to_passive     true
% 7.25/1.61  --inst_prop_sim_given                   true
% 7.25/1.61  --inst_prop_sim_new                     false
% 7.25/1.61  --inst_subs_new                         false
% 7.25/1.61  --inst_eq_res_simp                      false
% 7.25/1.61  --inst_subs_given                       false
% 7.25/1.61  --inst_orphan_elimination               true
% 7.25/1.61  --inst_learning_loop_flag               true
% 7.25/1.61  --inst_learning_start                   3000
% 7.25/1.61  --inst_learning_factor                  2
% 7.25/1.61  --inst_start_prop_sim_after_learn       3
% 7.25/1.61  --inst_sel_renew                        solver
% 7.25/1.61  --inst_lit_activity_flag                true
% 7.25/1.61  --inst_restr_to_given                   false
% 7.25/1.61  --inst_activity_threshold               500
% 7.25/1.61  --inst_out_proof                        true
% 7.25/1.61  
% 7.25/1.61  ------ Resolution Options
% 7.25/1.61  
% 7.25/1.61  --resolution_flag                       true
% 7.25/1.61  --res_lit_sel                           adaptive
% 7.25/1.61  --res_lit_sel_side                      none
% 7.25/1.61  --res_ordering                          kbo
% 7.25/1.61  --res_to_prop_solver                    active
% 7.25/1.61  --res_prop_simpl_new                    false
% 7.25/1.61  --res_prop_simpl_given                  true
% 7.25/1.61  --res_passive_queue_type                priority_queues
% 7.25/1.61  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.25/1.61  --res_passive_queues_freq               [15;5]
% 7.25/1.61  --res_forward_subs                      full
% 7.25/1.61  --res_backward_subs                     full
% 7.25/1.61  --res_forward_subs_resolution           true
% 7.25/1.61  --res_backward_subs_resolution          true
% 7.25/1.61  --res_orphan_elimination                true
% 7.25/1.61  --res_time_limit                        2.
% 7.25/1.61  --res_out_proof                         true
% 7.25/1.61  
% 7.25/1.61  ------ Superposition Options
% 7.25/1.61  
% 7.25/1.61  --superposition_flag                    true
% 7.25/1.61  --sup_passive_queue_type                priority_queues
% 7.25/1.61  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.25/1.61  --sup_passive_queues_freq               [8;1;4]
% 7.25/1.61  --demod_completeness_check              fast
% 7.25/1.61  --demod_use_ground                      true
% 7.25/1.61  --sup_to_prop_solver                    passive
% 7.25/1.61  --sup_prop_simpl_new                    true
% 7.25/1.61  --sup_prop_simpl_given                  true
% 7.25/1.61  --sup_fun_splitting                     false
% 7.25/1.61  --sup_smt_interval                      50000
% 7.25/1.61  
% 7.25/1.61  ------ Superposition Simplification Setup
% 7.25/1.61  
% 7.25/1.61  --sup_indices_passive                   []
% 7.25/1.61  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.61  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.61  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.61  --sup_full_triv                         [TrivRules;PropSubs]
% 7.25/1.61  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.61  --sup_full_bw                           [BwDemod]
% 7.25/1.61  --sup_immed_triv                        [TrivRules]
% 7.25/1.61  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.25/1.61  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.61  --sup_immed_bw_main                     []
% 7.25/1.61  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.25/1.61  --sup_input_triv                        [Unflattening;TrivRules]
% 7.25/1.61  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.61  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.25/1.61  
% 7.25/1.61  ------ Combination Options
% 7.25/1.61  
% 7.25/1.61  --comb_res_mult                         3
% 7.25/1.61  --comb_sup_mult                         2
% 7.25/1.61  --comb_inst_mult                        10
% 7.25/1.61  
% 7.25/1.61  ------ Debug Options
% 7.25/1.61  
% 7.25/1.61  --dbg_backtrace                         false
% 7.25/1.61  --dbg_dump_prop_clauses                 false
% 7.25/1.61  --dbg_dump_prop_clauses_file            -
% 7.25/1.61  --dbg_out_stat                          false
% 7.25/1.61  ------ Parsing...
% 7.25/1.61  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.25/1.61  
% 7.25/1.61  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.25/1.61  
% 7.25/1.61  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.25/1.61  
% 7.25/1.61  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.25/1.61  ------ Proving...
% 7.25/1.61  ------ Problem Properties 
% 7.25/1.61  
% 7.25/1.61  
% 7.25/1.61  clauses                                 44
% 7.25/1.61  conjectures                             10
% 7.25/1.61  EPR                                     16
% 7.25/1.61  Horn                                    38
% 7.25/1.61  unary                                   15
% 7.25/1.61  binary                                  11
% 7.25/1.61  lits                                    117
% 7.25/1.61  lits eq                                 12
% 7.25/1.61  fd_pure                                 0
% 7.25/1.61  fd_pseudo                               0
% 7.25/1.61  fd_cond                                 5
% 7.25/1.61  fd_pseudo_cond                          1
% 7.25/1.61  AC symbols                              0
% 7.25/1.61  
% 7.25/1.61  ------ Schedule dynamic 5 is on 
% 7.25/1.61  
% 7.25/1.61  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.25/1.61  
% 7.25/1.61  
% 7.25/1.61  ------ 
% 7.25/1.61  Current options:
% 7.25/1.61  ------ 
% 7.25/1.61  
% 7.25/1.61  ------ Input Options
% 7.25/1.61  
% 7.25/1.61  --out_options                           all
% 7.25/1.61  --tptp_safe_out                         true
% 7.25/1.61  --problem_path                          ""
% 7.25/1.61  --include_path                          ""
% 7.25/1.61  --clausifier                            res/vclausify_rel
% 7.25/1.61  --clausifier_options                    --mode clausify
% 7.25/1.61  --stdin                                 false
% 7.25/1.61  --stats_out                             all
% 7.25/1.61  
% 7.25/1.61  ------ General Options
% 7.25/1.61  
% 7.25/1.61  --fof                                   false
% 7.25/1.61  --time_out_real                         305.
% 7.25/1.61  --time_out_virtual                      -1.
% 7.25/1.61  --symbol_type_check                     false
% 7.25/1.61  --clausify_out                          false
% 7.25/1.61  --sig_cnt_out                           false
% 7.25/1.61  --trig_cnt_out                          false
% 7.25/1.61  --trig_cnt_out_tolerance                1.
% 7.25/1.61  --trig_cnt_out_sk_spl                   false
% 7.25/1.61  --abstr_cl_out                          false
% 7.25/1.61  
% 7.25/1.61  ------ Global Options
% 7.25/1.61  
% 7.25/1.61  --schedule                              default
% 7.25/1.61  --add_important_lit                     false
% 7.25/1.61  --prop_solver_per_cl                    1000
% 7.25/1.61  --min_unsat_core                        false
% 7.25/1.61  --soft_assumptions                      false
% 7.25/1.61  --soft_lemma_size                       3
% 7.25/1.61  --prop_impl_unit_size                   0
% 7.25/1.61  --prop_impl_unit                        []
% 7.25/1.61  --share_sel_clauses                     true
% 7.25/1.61  --reset_solvers                         false
% 7.25/1.61  --bc_imp_inh                            [conj_cone]
% 7.25/1.61  --conj_cone_tolerance                   3.
% 7.25/1.61  --extra_neg_conj                        none
% 7.25/1.61  --large_theory_mode                     true
% 7.25/1.61  --prolific_symb_bound                   200
% 7.25/1.61  --lt_threshold                          2000
% 7.25/1.61  --clause_weak_htbl                      true
% 7.25/1.61  --gc_record_bc_elim                     false
% 7.25/1.61  
% 7.25/1.61  ------ Preprocessing Options
% 7.25/1.61  
% 7.25/1.61  --preprocessing_flag                    true
% 7.25/1.61  --time_out_prep_mult                    0.1
% 7.25/1.61  --splitting_mode                        input
% 7.25/1.61  --splitting_grd                         true
% 7.25/1.61  --splitting_cvd                         false
% 7.25/1.61  --splitting_cvd_svl                     false
% 7.25/1.61  --splitting_nvd                         32
% 7.25/1.61  --sub_typing                            true
% 7.25/1.61  --prep_gs_sim                           true
% 7.25/1.61  --prep_unflatten                        true
% 7.25/1.61  --prep_res_sim                          true
% 7.25/1.61  --prep_upred                            true
% 7.25/1.61  --prep_sem_filter                       exhaustive
% 7.25/1.61  --prep_sem_filter_out                   false
% 7.25/1.61  --pred_elim                             true
% 7.25/1.61  --res_sim_input                         true
% 7.25/1.61  --eq_ax_congr_red                       true
% 7.25/1.61  --pure_diseq_elim                       true
% 7.25/1.61  --brand_transform                       false
% 7.25/1.61  --non_eq_to_eq                          false
% 7.25/1.61  --prep_def_merge                        true
% 7.25/1.61  --prep_def_merge_prop_impl              false
% 7.25/1.61  --prep_def_merge_mbd                    true
% 7.25/1.61  --prep_def_merge_tr_red                 false
% 7.25/1.61  --prep_def_merge_tr_cl                  false
% 7.25/1.61  --smt_preprocessing                     true
% 7.25/1.61  --smt_ac_axioms                         fast
% 7.25/1.61  --preprocessed_out                      false
% 7.25/1.61  --preprocessed_stats                    false
% 7.25/1.61  
% 7.25/1.61  ------ Abstraction refinement Options
% 7.25/1.61  
% 7.25/1.61  --abstr_ref                             []
% 7.25/1.61  --abstr_ref_prep                        false
% 7.25/1.61  --abstr_ref_until_sat                   false
% 7.25/1.61  --abstr_ref_sig_restrict                funpre
% 7.25/1.61  --abstr_ref_af_restrict_to_split_sk     false
% 7.25/1.61  --abstr_ref_under                       []
% 7.25/1.61  
% 7.25/1.61  ------ SAT Options
% 7.25/1.61  
% 7.25/1.61  --sat_mode                              false
% 7.25/1.61  --sat_fm_restart_options                ""
% 7.25/1.61  --sat_gr_def                            false
% 7.25/1.61  --sat_epr_types                         true
% 7.25/1.61  --sat_non_cyclic_types                  false
% 7.25/1.61  --sat_finite_models                     false
% 7.25/1.61  --sat_fm_lemmas                         false
% 7.25/1.61  --sat_fm_prep                           false
% 7.25/1.61  --sat_fm_uc_incr                        true
% 7.25/1.61  --sat_out_model                         small
% 7.25/1.61  --sat_out_clauses                       false
% 7.25/1.61  
% 7.25/1.61  ------ QBF Options
% 7.25/1.61  
% 7.25/1.61  --qbf_mode                              false
% 7.25/1.61  --qbf_elim_univ                         false
% 7.25/1.61  --qbf_dom_inst                          none
% 7.25/1.61  --qbf_dom_pre_inst                      false
% 7.25/1.61  --qbf_sk_in                             false
% 7.25/1.61  --qbf_pred_elim                         true
% 7.25/1.61  --qbf_split                             512
% 7.25/1.61  
% 7.25/1.61  ------ BMC1 Options
% 7.25/1.61  
% 7.25/1.61  --bmc1_incremental                      false
% 7.25/1.61  --bmc1_axioms                           reachable_all
% 7.25/1.61  --bmc1_min_bound                        0
% 7.25/1.61  --bmc1_max_bound                        -1
% 7.25/1.61  --bmc1_max_bound_default                -1
% 7.25/1.61  --bmc1_symbol_reachability              true
% 7.25/1.61  --bmc1_property_lemmas                  false
% 7.25/1.61  --bmc1_k_induction                      false
% 7.25/1.61  --bmc1_non_equiv_states                 false
% 7.25/1.61  --bmc1_deadlock                         false
% 7.25/1.61  --bmc1_ucm                              false
% 7.25/1.61  --bmc1_add_unsat_core                   none
% 7.25/1.61  --bmc1_unsat_core_children              false
% 7.25/1.61  --bmc1_unsat_core_extrapolate_axioms    false
% 7.25/1.61  --bmc1_out_stat                         full
% 7.25/1.61  --bmc1_ground_init                      false
% 7.25/1.61  --bmc1_pre_inst_next_state              false
% 7.25/1.61  --bmc1_pre_inst_state                   false
% 7.25/1.61  --bmc1_pre_inst_reach_state             false
% 7.25/1.61  --bmc1_out_unsat_core                   false
% 7.25/1.61  --bmc1_aig_witness_out                  false
% 7.25/1.61  --bmc1_verbose                          false
% 7.25/1.61  --bmc1_dump_clauses_tptp                false
% 7.25/1.61  --bmc1_dump_unsat_core_tptp             false
% 7.25/1.61  --bmc1_dump_file                        -
% 7.25/1.61  --bmc1_ucm_expand_uc_limit              128
% 7.25/1.61  --bmc1_ucm_n_expand_iterations          6
% 7.25/1.61  --bmc1_ucm_extend_mode                  1
% 7.25/1.61  --bmc1_ucm_init_mode                    2
% 7.25/1.61  --bmc1_ucm_cone_mode                    none
% 7.25/1.61  --bmc1_ucm_reduced_relation_type        0
% 7.25/1.61  --bmc1_ucm_relax_model                  4
% 7.25/1.61  --bmc1_ucm_full_tr_after_sat            true
% 7.25/1.61  --bmc1_ucm_expand_neg_assumptions       false
% 7.25/1.61  --bmc1_ucm_layered_model                none
% 7.25/1.61  --bmc1_ucm_max_lemma_size               10
% 7.25/1.61  
% 7.25/1.61  ------ AIG Options
% 7.25/1.61  
% 7.25/1.61  --aig_mode                              false
% 7.25/1.61  
% 7.25/1.61  ------ Instantiation Options
% 7.25/1.61  
% 7.25/1.61  --instantiation_flag                    true
% 7.25/1.61  --inst_sos_flag                         false
% 7.25/1.61  --inst_sos_phase                        true
% 7.25/1.61  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.25/1.61  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.25/1.61  --inst_lit_sel_side                     none
% 7.25/1.61  --inst_solver_per_active                1400
% 7.25/1.61  --inst_solver_calls_frac                1.
% 7.25/1.61  --inst_passive_queue_type               priority_queues
% 7.25/1.61  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.25/1.61  --inst_passive_queues_freq              [25;2]
% 7.25/1.61  --inst_dismatching                      true
% 7.25/1.61  --inst_eager_unprocessed_to_passive     true
% 7.25/1.61  --inst_prop_sim_given                   true
% 7.25/1.61  --inst_prop_sim_new                     false
% 7.25/1.61  --inst_subs_new                         false
% 7.25/1.61  --inst_eq_res_simp                      false
% 7.25/1.61  --inst_subs_given                       false
% 7.25/1.61  --inst_orphan_elimination               true
% 7.25/1.61  --inst_learning_loop_flag               true
% 7.25/1.61  --inst_learning_start                   3000
% 7.25/1.61  --inst_learning_factor                  2
% 7.25/1.61  --inst_start_prop_sim_after_learn       3
% 7.25/1.61  --inst_sel_renew                        solver
% 7.25/1.61  --inst_lit_activity_flag                true
% 7.25/1.61  --inst_restr_to_given                   false
% 7.25/1.61  --inst_activity_threshold               500
% 7.25/1.61  --inst_out_proof                        true
% 7.25/1.61  
% 7.25/1.61  ------ Resolution Options
% 7.25/1.61  
% 7.25/1.61  --resolution_flag                       false
% 7.25/1.61  --res_lit_sel                           adaptive
% 7.25/1.61  --res_lit_sel_side                      none
% 7.25/1.61  --res_ordering                          kbo
% 7.25/1.61  --res_to_prop_solver                    active
% 7.25/1.61  --res_prop_simpl_new                    false
% 7.25/1.61  --res_prop_simpl_given                  true
% 7.25/1.61  --res_passive_queue_type                priority_queues
% 7.25/1.61  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.25/1.61  --res_passive_queues_freq               [15;5]
% 7.25/1.61  --res_forward_subs                      full
% 7.25/1.61  --res_backward_subs                     full
% 7.25/1.61  --res_forward_subs_resolution           true
% 7.25/1.61  --res_backward_subs_resolution          true
% 7.25/1.61  --res_orphan_elimination                true
% 7.25/1.61  --res_time_limit                        2.
% 7.25/1.61  --res_out_proof                         true
% 7.25/1.61  
% 7.25/1.61  ------ Superposition Options
% 7.25/1.61  
% 7.25/1.61  --superposition_flag                    true
% 7.25/1.61  --sup_passive_queue_type                priority_queues
% 7.25/1.61  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.25/1.61  --sup_passive_queues_freq               [8;1;4]
% 7.25/1.61  --demod_completeness_check              fast
% 7.25/1.61  --demod_use_ground                      true
% 7.25/1.61  --sup_to_prop_solver                    passive
% 7.25/1.61  --sup_prop_simpl_new                    true
% 7.25/1.61  --sup_prop_simpl_given                  true
% 7.25/1.61  --sup_fun_splitting                     false
% 7.25/1.61  --sup_smt_interval                      50000
% 7.25/1.61  
% 7.25/1.61  ------ Superposition Simplification Setup
% 7.25/1.61  
% 7.25/1.61  --sup_indices_passive                   []
% 7.25/1.61  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.61  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.61  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.61  --sup_full_triv                         [TrivRules;PropSubs]
% 7.25/1.61  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.61  --sup_full_bw                           [BwDemod]
% 7.25/1.61  --sup_immed_triv                        [TrivRules]
% 7.25/1.61  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.25/1.61  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.61  --sup_immed_bw_main                     []
% 7.25/1.61  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.25/1.61  --sup_input_triv                        [Unflattening;TrivRules]
% 7.25/1.61  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.61  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.25/1.61  
% 7.25/1.61  ------ Combination Options
% 7.25/1.61  
% 7.25/1.61  --comb_res_mult                         3
% 7.25/1.61  --comb_sup_mult                         2
% 7.25/1.61  --comb_inst_mult                        10
% 7.25/1.61  
% 7.25/1.61  ------ Debug Options
% 7.25/1.61  
% 7.25/1.61  --dbg_backtrace                         false
% 7.25/1.61  --dbg_dump_prop_clauses                 false
% 7.25/1.61  --dbg_dump_prop_clauses_file            -
% 7.25/1.61  --dbg_out_stat                          false
% 7.25/1.61  
% 7.25/1.61  
% 7.25/1.61  
% 7.25/1.61  
% 7.25/1.61  ------ Proving...
% 7.25/1.61  
% 7.25/1.61  
% 7.25/1.61  % SZS status Theorem for theBenchmark.p
% 7.25/1.61  
% 7.25/1.61  % SZS output start CNFRefutation for theBenchmark.p
% 7.25/1.61  
% 7.25/1.61  fof(f27,conjecture,(
% 7.25/1.61    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f28,negated_conjecture,(
% 7.25/1.61    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 7.25/1.61    inference(negated_conjecture,[],[f27])).
% 7.25/1.61  
% 7.25/1.61  fof(f58,plain,(
% 7.25/1.61    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 7.25/1.61    inference(ennf_transformation,[],[f28])).
% 7.25/1.61  
% 7.25/1.61  fof(f59,plain,(
% 7.25/1.61    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 7.25/1.61    inference(flattening,[],[f58])).
% 7.25/1.61  
% 7.25/1.61  fof(f70,plain,(
% 7.25/1.61    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k7_partfun1(X0,X4,k1_funct_1(X3,sK6)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK6) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK6,X1))) )),
% 7.25/1.61    introduced(choice_axiom,[])).
% 7.25/1.61  
% 7.25/1.61  fof(f69,plain,(
% 7.25/1.61    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k7_partfun1(X0,sK5,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK5),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK5)) & m1_subset_1(X5,X1)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK5))) )),
% 7.25/1.61    introduced(choice_axiom,[])).
% 7.25/1.61  
% 7.25/1.61  fof(f68,plain,(
% 7.25/1.61    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(sK4,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK4,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK4),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 7.25/1.61    introduced(choice_axiom,[])).
% 7.25/1.61  
% 7.25/1.61  fof(f67,plain,(
% 7.25/1.61    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(sK1,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))),
% 7.25/1.61    introduced(choice_axiom,[])).
% 7.25/1.61  
% 7.25/1.61  fof(f71,plain,(
% 7.25/1.61    (((k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) & m1_subset_1(sK6,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 7.25/1.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f59,f70,f69,f68,f67])).
% 7.25/1.61  
% 7.25/1.61  fof(f117,plain,(
% 7.25/1.61    m1_subset_1(sK6,sK2)),
% 7.25/1.61    inference(cnf_transformation,[],[f71])).
% 7.25/1.61  
% 7.25/1.61  fof(f8,axiom,(
% 7.25/1.61    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f32,plain,(
% 7.25/1.61    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.25/1.61    inference(ennf_transformation,[],[f8])).
% 7.25/1.61  
% 7.25/1.61  fof(f33,plain,(
% 7.25/1.61    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.25/1.61    inference(flattening,[],[f32])).
% 7.25/1.61  
% 7.25/1.61  fof(f81,plain,(
% 7.25/1.61    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.25/1.61    inference(cnf_transformation,[],[f33])).
% 7.25/1.61  
% 7.25/1.61  fof(f119,plain,(
% 7.25/1.61    k1_xboole_0 != sK2),
% 7.25/1.61    inference(cnf_transformation,[],[f71])).
% 7.25/1.61  
% 7.25/1.61  fof(f2,axiom,(
% 7.25/1.61    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f29,plain,(
% 7.25/1.61    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.25/1.61    inference(ennf_transformation,[],[f2])).
% 7.25/1.61  
% 7.25/1.61  fof(f73,plain,(
% 7.25/1.61    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.25/1.61    inference(cnf_transformation,[],[f29])).
% 7.25/1.61  
% 7.25/1.61  fof(f116,plain,(
% 7.25/1.61    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.25/1.61    inference(cnf_transformation,[],[f71])).
% 7.25/1.61  
% 7.25/1.61  fof(f19,axiom,(
% 7.25/1.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f45,plain,(
% 7.25/1.61    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.25/1.61    inference(ennf_transformation,[],[f19])).
% 7.25/1.61  
% 7.25/1.61  fof(f96,plain,(
% 7.25/1.61    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.25/1.61    inference(cnf_transformation,[],[f45])).
% 7.25/1.61  
% 7.25/1.61  fof(f114,plain,(
% 7.25/1.61    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 7.25/1.61    inference(cnf_transformation,[],[f71])).
% 7.25/1.61  
% 7.25/1.61  fof(f21,axiom,(
% 7.25/1.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f47,plain,(
% 7.25/1.61    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.25/1.61    inference(ennf_transformation,[],[f21])).
% 7.25/1.61  
% 7.25/1.61  fof(f98,plain,(
% 7.25/1.61    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.25/1.61    inference(cnf_transformation,[],[f47])).
% 7.25/1.61  
% 7.25/1.61  fof(f118,plain,(
% 7.25/1.61    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))),
% 7.25/1.61    inference(cnf_transformation,[],[f71])).
% 7.25/1.61  
% 7.25/1.61  fof(f20,axiom,(
% 7.25/1.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f46,plain,(
% 7.25/1.61    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.25/1.61    inference(ennf_transformation,[],[f20])).
% 7.25/1.61  
% 7.25/1.61  fof(f97,plain,(
% 7.25/1.61    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.25/1.61    inference(cnf_transformation,[],[f46])).
% 7.25/1.61  
% 7.25/1.61  fof(f26,axiom,(
% 7.25/1.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f56,plain,(
% 7.25/1.61    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.25/1.61    inference(ennf_transformation,[],[f26])).
% 7.25/1.61  
% 7.25/1.61  fof(f57,plain,(
% 7.25/1.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.25/1.61    inference(flattening,[],[f56])).
% 7.25/1.61  
% 7.25/1.61  fof(f109,plain,(
% 7.25/1.61    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.25/1.61    inference(cnf_transformation,[],[f57])).
% 7.25/1.61  
% 7.25/1.61  fof(f111,plain,(
% 7.25/1.61    ~v1_xboole_0(sK3)),
% 7.25/1.61    inference(cnf_transformation,[],[f71])).
% 7.25/1.61  
% 7.25/1.61  fof(f112,plain,(
% 7.25/1.61    v1_funct_1(sK4)),
% 7.25/1.61    inference(cnf_transformation,[],[f71])).
% 7.25/1.61  
% 7.25/1.61  fof(f113,plain,(
% 7.25/1.61    v1_funct_2(sK4,sK2,sK3)),
% 7.25/1.61    inference(cnf_transformation,[],[f71])).
% 7.25/1.61  
% 7.25/1.61  fof(f1,axiom,(
% 7.25/1.61    v1_xboole_0(k1_xboole_0)),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f72,plain,(
% 7.25/1.61    v1_xboole_0(k1_xboole_0)),
% 7.25/1.61    inference(cnf_transformation,[],[f1])).
% 7.25/1.61  
% 7.25/1.61  fof(f25,axiom,(
% 7.25/1.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f54,plain,(
% 7.25/1.61    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.25/1.61    inference(ennf_transformation,[],[f25])).
% 7.25/1.61  
% 7.25/1.61  fof(f55,plain,(
% 7.25/1.61    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.25/1.61    inference(flattening,[],[f54])).
% 7.25/1.61  
% 7.25/1.61  fof(f104,plain,(
% 7.25/1.61    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.25/1.61    inference(cnf_transformation,[],[f55])).
% 7.25/1.61  
% 7.25/1.61  fof(f107,plain,(
% 7.25/1.61    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.25/1.61    inference(cnf_transformation,[],[f57])).
% 7.25/1.61  
% 7.25/1.61  fof(f23,axiom,(
% 7.25/1.61    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f50,plain,(
% 7.25/1.61    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.25/1.61    inference(ennf_transformation,[],[f23])).
% 7.25/1.61  
% 7.25/1.61  fof(f51,plain,(
% 7.25/1.61    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.25/1.61    inference(flattening,[],[f50])).
% 7.25/1.61  
% 7.25/1.61  fof(f102,plain,(
% 7.25/1.61    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.25/1.61    inference(cnf_transformation,[],[f51])).
% 7.25/1.61  
% 7.25/1.61  fof(f115,plain,(
% 7.25/1.61    v1_funct_1(sK5)),
% 7.25/1.61    inference(cnf_transformation,[],[f71])).
% 7.25/1.61  
% 7.25/1.61  fof(f4,axiom,(
% 7.25/1.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f77,plain,(
% 7.25/1.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.25/1.61    inference(cnf_transformation,[],[f4])).
% 7.25/1.61  
% 7.25/1.61  fof(f3,axiom,(
% 7.25/1.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f60,plain,(
% 7.25/1.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.25/1.61    inference(nnf_transformation,[],[f3])).
% 7.25/1.61  
% 7.25/1.61  fof(f61,plain,(
% 7.25/1.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.25/1.61    inference(flattening,[],[f60])).
% 7.25/1.61  
% 7.25/1.61  fof(f76,plain,(
% 7.25/1.61    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.25/1.61    inference(cnf_transformation,[],[f61])).
% 7.25/1.61  
% 7.25/1.61  fof(f18,axiom,(
% 7.25/1.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f44,plain,(
% 7.25/1.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.25/1.61    inference(ennf_transformation,[],[f18])).
% 7.25/1.61  
% 7.25/1.61  fof(f94,plain,(
% 7.25/1.61    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.25/1.61    inference(cnf_transformation,[],[f44])).
% 7.25/1.61  
% 7.25/1.61  fof(f12,axiom,(
% 7.25/1.61    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f37,plain,(
% 7.25/1.61    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.25/1.61    inference(ennf_transformation,[],[f12])).
% 7.25/1.61  
% 7.25/1.61  fof(f66,plain,(
% 7.25/1.61    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.25/1.61    inference(nnf_transformation,[],[f37])).
% 7.25/1.61  
% 7.25/1.61  fof(f87,plain,(
% 7.25/1.61    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.25/1.61    inference(cnf_transformation,[],[f66])).
% 7.25/1.61  
% 7.25/1.61  fof(f22,axiom,(
% 7.25/1.61    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f48,plain,(
% 7.25/1.61    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.25/1.61    inference(ennf_transformation,[],[f22])).
% 7.25/1.61  
% 7.25/1.61  fof(f49,plain,(
% 7.25/1.61    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.25/1.61    inference(flattening,[],[f48])).
% 7.25/1.61  
% 7.25/1.61  fof(f100,plain,(
% 7.25/1.61    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.25/1.61    inference(cnf_transformation,[],[f49])).
% 7.25/1.61  
% 7.25/1.61  fof(f16,axiom,(
% 7.25/1.61    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f42,plain,(
% 7.25/1.61    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 7.25/1.61    inference(ennf_transformation,[],[f16])).
% 7.25/1.61  
% 7.25/1.61  fof(f92,plain,(
% 7.25/1.61    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 7.25/1.61    inference(cnf_transformation,[],[f42])).
% 7.25/1.61  
% 7.25/1.61  fof(f14,axiom,(
% 7.25/1.61    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f38,plain,(
% 7.25/1.61    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 7.25/1.61    inference(ennf_transformation,[],[f14])).
% 7.25/1.61  
% 7.25/1.61  fof(f39,plain,(
% 7.25/1.61    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 7.25/1.61    inference(flattening,[],[f38])).
% 7.25/1.61  
% 7.25/1.61  fof(f90,plain,(
% 7.25/1.61    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 7.25/1.61    inference(cnf_transformation,[],[f39])).
% 7.25/1.61  
% 7.25/1.61  fof(f7,axiom,(
% 7.25/1.61    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f31,plain,(
% 7.25/1.61    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 7.25/1.61    inference(ennf_transformation,[],[f7])).
% 7.25/1.61  
% 7.25/1.61  fof(f80,plain,(
% 7.25/1.61    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.25/1.61    inference(cnf_transformation,[],[f31])).
% 7.25/1.61  
% 7.25/1.61  fof(f9,axiom,(
% 7.25/1.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f64,plain,(
% 7.25/1.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.25/1.61    inference(nnf_transformation,[],[f9])).
% 7.25/1.61  
% 7.25/1.61  fof(f83,plain,(
% 7.25/1.61    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.25/1.61    inference(cnf_transformation,[],[f64])).
% 7.25/1.61  
% 7.25/1.61  fof(f88,plain,(
% 7.25/1.61    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.25/1.61    inference(cnf_transformation,[],[f66])).
% 7.25/1.61  
% 7.25/1.61  fof(f15,axiom,(
% 7.25/1.61    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_relat_1(X2,X0) & v1_relat_1(X2)) => v5_relat_1(X2,X1)))),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f40,plain,(
% 7.25/1.61    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | (~v5_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 7.25/1.61    inference(ennf_transformation,[],[f15])).
% 7.25/1.61  
% 7.25/1.61  fof(f41,plain,(
% 7.25/1.61    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 7.25/1.61    inference(flattening,[],[f40])).
% 7.25/1.61  
% 7.25/1.61  fof(f91,plain,(
% 7.25/1.61    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1)) )),
% 7.25/1.61    inference(cnf_transformation,[],[f41])).
% 7.25/1.61  
% 7.25/1.61  fof(f24,axiom,(
% 7.25/1.61    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 7.25/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.61  
% 7.25/1.61  fof(f52,plain,(
% 7.25/1.61    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 7.25/1.61    inference(ennf_transformation,[],[f24])).
% 7.25/1.61  
% 7.25/1.61  fof(f53,plain,(
% 7.25/1.61    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 7.25/1.61    inference(flattening,[],[f52])).
% 7.25/1.61  
% 7.25/1.61  fof(f103,plain,(
% 7.25/1.61    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 7.25/1.61    inference(cnf_transformation,[],[f53])).
% 7.25/1.61  
% 7.25/1.61  fof(f120,plain,(
% 7.25/1.61    k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6)),
% 7.25/1.61    inference(cnf_transformation,[],[f71])).
% 7.25/1.61  
% 7.25/1.61  cnf(c_42,negated_conjecture,
% 7.25/1.61      ( m1_subset_1(sK6,sK2) ),
% 7.25/1.61      inference(cnf_transformation,[],[f117]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2385,plain,
% 7.25/1.61      ( m1_subset_1(sK6,sK2) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_9,plain,
% 7.25/1.61      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 7.25/1.61      inference(cnf_transformation,[],[f81]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2411,plain,
% 7.25/1.61      ( r2_hidden(X0,X1) = iProver_top
% 7.25/1.61      | m1_subset_1(X0,X1) != iProver_top
% 7.25/1.61      | v1_xboole_0(X1) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_5516,plain,
% 7.25/1.61      ( r2_hidden(sK6,sK2) = iProver_top
% 7.25/1.61      | v1_xboole_0(sK2) = iProver_top ),
% 7.25/1.61      inference(superposition,[status(thm)],[c_2385,c_2411]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_55,plain,
% 7.25/1.61      ( m1_subset_1(sK6,sK2) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_40,negated_conjecture,
% 7.25/1.61      ( k1_xboole_0 != sK2 ),
% 7.25/1.61      inference(cnf_transformation,[],[f119]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_1,plain,
% 7.25/1.61      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.25/1.61      inference(cnf_transformation,[],[f73]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2746,plain,
% 7.25/1.61      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_1]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2747,plain,
% 7.25/1.61      ( k1_xboole_0 = sK2 | v1_xboole_0(sK2) != iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_2746]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2934,plain,
% 7.25/1.61      ( r2_hidden(X0,sK2) | ~ m1_subset_1(X0,sK2) | v1_xboole_0(sK2) ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_9]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_3252,plain,
% 7.25/1.61      ( r2_hidden(sK6,sK2) | ~ m1_subset_1(sK6,sK2) | v1_xboole_0(sK2) ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_2934]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_3253,plain,
% 7.25/1.61      ( r2_hidden(sK6,sK2) = iProver_top
% 7.25/1.61      | m1_subset_1(sK6,sK2) != iProver_top
% 7.25/1.61      | v1_xboole_0(sK2) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_3252]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_5806,plain,
% 7.25/1.61      ( r2_hidden(sK6,sK2) = iProver_top ),
% 7.25/1.61      inference(global_propositional_subsumption,
% 7.25/1.61                [status(thm)],
% 7.25/1.61                [c_5516,c_55,c_40,c_2747,c_3253]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_43,negated_conjecture,
% 7.25/1.61      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.25/1.61      inference(cnf_transformation,[],[f116]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2384,plain,
% 7.25/1.61      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_23,plain,
% 7.25/1.61      ( v5_relat_1(X0,X1)
% 7.25/1.61      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.25/1.61      inference(cnf_transformation,[],[f96]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2397,plain,
% 7.25/1.61      ( v5_relat_1(X0,X1) = iProver_top
% 7.25/1.61      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_4316,plain,
% 7.25/1.61      ( v5_relat_1(sK5,sK1) = iProver_top ),
% 7.25/1.61      inference(superposition,[status(thm)],[c_2384,c_2397]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_45,negated_conjecture,
% 7.25/1.61      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 7.25/1.61      inference(cnf_transformation,[],[f114]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2382,plain,
% 7.25/1.61      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_26,plain,
% 7.25/1.61      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.25/1.61      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.25/1.61      inference(cnf_transformation,[],[f98]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2394,plain,
% 7.25/1.61      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.25/1.61      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_4342,plain,
% 7.25/1.61      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 7.25/1.61      inference(superposition,[status(thm)],[c_2382,c_2394]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_41,negated_conjecture,
% 7.25/1.61      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
% 7.25/1.61      inference(cnf_transformation,[],[f118]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2386,plain,
% 7.25/1.61      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_4893,plain,
% 7.25/1.61      ( r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
% 7.25/1.61      inference(demodulation,[status(thm)],[c_4342,c_2386]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_25,plain,
% 7.25/1.61      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.25/1.61      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.25/1.61      inference(cnf_transformation,[],[f97]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2395,plain,
% 7.25/1.61      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.25/1.61      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_5103,plain,
% 7.25/1.61      ( k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5) ),
% 7.25/1.61      inference(superposition,[status(thm)],[c_2384,c_2395]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_5707,plain,
% 7.25/1.61      ( r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) = iProver_top ),
% 7.25/1.61      inference(light_normalisation,[status(thm)],[c_4893,c_5103]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_34,plain,
% 7.25/1.61      ( ~ v1_funct_2(X0,X1,X2)
% 7.25/1.61      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.25/1.61      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.25/1.61      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 7.25/1.61      | ~ v1_funct_1(X0)
% 7.25/1.61      | k1_xboole_0 = X2 ),
% 7.25/1.61      inference(cnf_transformation,[],[f109]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2389,plain,
% 7.25/1.61      ( k1_xboole_0 = X0
% 7.25/1.61      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.25/1.61      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.25/1.61      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 7.25/1.61      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 7.25/1.61      | v1_funct_1(X1) != iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_6073,plain,
% 7.25/1.61      ( sK3 = k1_xboole_0
% 7.25/1.61      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 7.25/1.61      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.25/1.61      | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top
% 7.25/1.61      | v1_funct_1(sK4) != iProver_top ),
% 7.25/1.61      inference(superposition,[status(thm)],[c_2382,c_2389]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_6079,plain,
% 7.25/1.61      ( sK3 = k1_xboole_0
% 7.25/1.61      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 7.25/1.61      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.25/1.61      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 7.25/1.61      | v1_funct_1(sK4) != iProver_top ),
% 7.25/1.61      inference(light_normalisation,[status(thm)],[c_6073,c_4342]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_48,negated_conjecture,
% 7.25/1.61      ( ~ v1_xboole_0(sK3) ),
% 7.25/1.61      inference(cnf_transformation,[],[f111]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_47,negated_conjecture,
% 7.25/1.61      ( v1_funct_1(sK4) ),
% 7.25/1.61      inference(cnf_transformation,[],[f112]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_50,plain,
% 7.25/1.61      ( v1_funct_1(sK4) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_46,negated_conjecture,
% 7.25/1.61      ( v1_funct_2(sK4,sK2,sK3) ),
% 7.25/1.61      inference(cnf_transformation,[],[f113]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_51,plain,
% 7.25/1.61      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_0,plain,
% 7.25/1.61      ( v1_xboole_0(k1_xboole_0) ),
% 7.25/1.61      inference(cnf_transformation,[],[f72]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_1435,plain,
% 7.25/1.61      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.25/1.61      theory(equality) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2796,plain,
% 7.25/1.61      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_1435]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2798,plain,
% 7.25/1.61      ( v1_xboole_0(sK3)
% 7.25/1.61      | ~ v1_xboole_0(k1_xboole_0)
% 7.25/1.61      | sK3 != k1_xboole_0 ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_2796]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_6961,plain,
% 7.25/1.61      ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 7.25/1.61      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 7.25/1.61      inference(global_propositional_subsumption,
% 7.25/1.61                [status(thm)],
% 7.25/1.61                [c_6079,c_48,c_50,c_51,c_0,c_2798]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_6962,plain,
% 7.25/1.61      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.25/1.61      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
% 7.25/1.61      inference(renaming,[status(thm)],[c_6961]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_32,plain,
% 7.25/1.61      ( ~ v1_funct_2(X0,X1,X2)
% 7.25/1.61      | ~ r2_hidden(X3,X1)
% 7.25/1.61      | r2_hidden(k1_funct_1(X0,X3),X2)
% 7.25/1.61      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.25/1.61      | ~ v1_funct_1(X0)
% 7.25/1.61      | k1_xboole_0 = X2 ),
% 7.25/1.61      inference(cnf_transformation,[],[f104]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2391,plain,
% 7.25/1.61      ( k1_xboole_0 = X0
% 7.25/1.61      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.25/1.61      | r2_hidden(X3,X2) != iProver_top
% 7.25/1.61      | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
% 7.25/1.61      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.25/1.61      | v1_funct_1(X1) != iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_7611,plain,
% 7.25/1.61      ( k1_xboole_0 = X0
% 7.25/1.61      | v1_funct_2(sK4,sK2,X0) != iProver_top
% 7.25/1.61      | r2_hidden(X1,sK2) != iProver_top
% 7.25/1.61      | r2_hidden(k1_funct_1(sK4,X1),X0) = iProver_top
% 7.25/1.61      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 7.25/1.61      | v1_funct_1(sK4) != iProver_top ),
% 7.25/1.61      inference(superposition,[status(thm)],[c_6962,c_2391]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_36,plain,
% 7.25/1.61      ( ~ v1_funct_2(X0,X1,X2)
% 7.25/1.61      | v1_funct_2(X0,X1,X3)
% 7.25/1.61      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.25/1.61      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 7.25/1.61      | ~ v1_funct_1(X0)
% 7.25/1.61      | k1_xboole_0 = X2 ),
% 7.25/1.61      inference(cnf_transformation,[],[f107]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2387,plain,
% 7.25/1.61      ( k1_xboole_0 = X0
% 7.25/1.61      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.25/1.61      | v1_funct_2(X1,X2,X3) = iProver_top
% 7.25/1.61      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.25/1.61      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 7.25/1.61      | v1_funct_1(X1) != iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_4063,plain,
% 7.25/1.61      ( sK3 = k1_xboole_0
% 7.25/1.61      | v1_funct_2(sK4,sK2,X0) = iProver_top
% 7.25/1.61      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 7.25/1.61      | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top
% 7.25/1.61      | v1_funct_1(sK4) != iProver_top ),
% 7.25/1.61      inference(superposition,[status(thm)],[c_2382,c_2387]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_6043,plain,
% 7.25/1.61      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top
% 7.25/1.61      | v1_funct_2(sK4,sK2,X0) = iProver_top ),
% 7.25/1.61      inference(global_propositional_subsumption,
% 7.25/1.61                [status(thm)],
% 7.25/1.61                [c_4063,c_48,c_50,c_51,c_0,c_2798]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_6044,plain,
% 7.25/1.61      ( v1_funct_2(sK4,sK2,X0) = iProver_top
% 7.25/1.61      | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top ),
% 7.25/1.61      inference(renaming,[status(thm)],[c_6043]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_6049,plain,
% 7.25/1.61      ( v1_funct_2(sK4,sK2,X0) = iProver_top
% 7.25/1.61      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
% 7.25/1.61      inference(light_normalisation,[status(thm)],[c_6044,c_4342]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_13072,plain,
% 7.25/1.61      ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 7.25/1.61      | r2_hidden(k1_funct_1(sK4,X1),X0) = iProver_top
% 7.25/1.61      | r2_hidden(X1,sK2) != iProver_top
% 7.25/1.61      | k1_xboole_0 = X0 ),
% 7.25/1.61      inference(global_propositional_subsumption,
% 7.25/1.61                [status(thm)],
% 7.25/1.61                [c_7611,c_50,c_6049]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_13073,plain,
% 7.25/1.61      ( k1_xboole_0 = X0
% 7.25/1.61      | r2_hidden(X1,sK2) != iProver_top
% 7.25/1.61      | r2_hidden(k1_funct_1(sK4,X1),X0) = iProver_top
% 7.25/1.61      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
% 7.25/1.61      inference(renaming,[status(thm)],[c_13072]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_30,plain,
% 7.25/1.61      ( ~ v5_relat_1(X0,X1)
% 7.25/1.61      | ~ r2_hidden(X2,k1_relat_1(X0))
% 7.25/1.61      | ~ v1_funct_1(X0)
% 7.25/1.61      | ~ v1_relat_1(X0)
% 7.25/1.61      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 7.25/1.61      inference(cnf_transformation,[],[f102]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2393,plain,
% 7.25/1.61      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 7.25/1.61      | v5_relat_1(X1,X0) != iProver_top
% 7.25/1.61      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 7.25/1.61      | v1_funct_1(X1) != iProver_top
% 7.25/1.61      | v1_relat_1(X1) != iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_13081,plain,
% 7.25/1.61      ( k7_partfun1(X0,X1,k1_funct_1(sK4,X2)) = k1_funct_1(X1,k1_funct_1(sK4,X2))
% 7.25/1.61      | k1_relat_1(X1) = k1_xboole_0
% 7.25/1.61      | v5_relat_1(X1,X0) != iProver_top
% 7.25/1.61      | r2_hidden(X2,sK2) != iProver_top
% 7.25/1.61      | r1_tarski(k2_relat_1(sK4),k1_relat_1(X1)) != iProver_top
% 7.25/1.61      | v1_funct_1(X1) != iProver_top
% 7.25/1.61      | v1_relat_1(X1) != iProver_top ),
% 7.25/1.61      inference(superposition,[status(thm)],[c_13073,c_2393]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_25426,plain,
% 7.25/1.61      ( k7_partfun1(X0,sK5,k1_funct_1(sK4,X1)) = k1_funct_1(sK5,k1_funct_1(sK4,X1))
% 7.25/1.61      | k1_relat_1(sK5) = k1_xboole_0
% 7.25/1.61      | v5_relat_1(sK5,X0) != iProver_top
% 7.25/1.61      | r2_hidden(X1,sK2) != iProver_top
% 7.25/1.61      | v1_funct_1(sK5) != iProver_top
% 7.25/1.61      | v1_relat_1(sK5) != iProver_top ),
% 7.25/1.61      inference(superposition,[status(thm)],[c_5707,c_13081]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_49,plain,
% 7.25/1.61      ( v1_xboole_0(sK3) != iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_52,plain,
% 7.25/1.61      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_44,negated_conjecture,
% 7.25/1.61      ( v1_funct_1(sK5) ),
% 7.25/1.61      inference(cnf_transformation,[],[f115]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_53,plain,
% 7.25/1.61      ( v1_funct_1(sK5) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_54,plain,
% 7.25/1.61      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_5,plain,
% 7.25/1.61      ( r1_tarski(k1_xboole_0,X0) ),
% 7.25/1.61      inference(cnf_transformation,[],[f77]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_133,plain,
% 7.25/1.61      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_5]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_132,plain,
% 7.25/1.61      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_134,plain,
% 7.25/1.61      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_132]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2,plain,
% 7.25/1.61      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.25/1.61      inference(cnf_transformation,[],[f76]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_138,plain,
% 7.25/1.61      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.25/1.61      | k1_xboole_0 = k1_xboole_0 ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_2]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_143,plain,
% 7.25/1.61      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_22,plain,
% 7.25/1.61      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.25/1.61      | v1_relat_1(X0) ),
% 7.25/1.61      inference(cnf_transformation,[],[f94]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2771,plain,
% 7.25/1.61      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.25/1.61      | v1_relat_1(sK5) ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_22]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2772,plain,
% 7.25/1.61      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.25/1.61      | v1_relat_1(sK5) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_2771]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2774,plain,
% 7.25/1.61      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 7.25/1.61      | v1_relat_1(sK4) ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_22]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2775,plain,
% 7.25/1.61      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 7.25/1.61      | v1_relat_1(sK4) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_2774]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_16,plain,
% 7.25/1.61      ( ~ v5_relat_1(X0,X1)
% 7.25/1.61      | r1_tarski(k2_relat_1(X0),X1)
% 7.25/1.61      | ~ v1_relat_1(X0) ),
% 7.25/1.61      inference(cnf_transformation,[],[f87]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2990,plain,
% 7.25/1.61      ( ~ v5_relat_1(sK4,X0)
% 7.25/1.61      | r1_tarski(k2_relat_1(sK4),X0)
% 7.25/1.61      | ~ v1_relat_1(sK4) ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_16]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_3006,plain,
% 7.25/1.61      ( v5_relat_1(sK4,X0) != iProver_top
% 7.25/1.61      | r1_tarski(k2_relat_1(sK4),X0) = iProver_top
% 7.25/1.61      | v1_relat_1(sK4) != iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_2990]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_3008,plain,
% 7.25/1.61      ( v5_relat_1(sK4,k1_xboole_0) != iProver_top
% 7.25/1.61      | r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top
% 7.25/1.61      | v1_relat_1(sK4) != iProver_top ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_3006]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_1436,plain,
% 7.25/1.61      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.25/1.61      theory(equality) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_3304,plain,
% 7.25/1.61      ( ~ r1_tarski(X0,X1)
% 7.25/1.61      | r1_tarski(k1_relat_1(sK5),X2)
% 7.25/1.61      | X2 != X1
% 7.25/1.61      | k1_relat_1(sK5) != X0 ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_1436]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_3305,plain,
% 7.25/1.61      ( X0 != X1
% 7.25/1.61      | k1_relat_1(sK5) != X2
% 7.25/1.61      | r1_tarski(X2,X1) != iProver_top
% 7.25/1.61      | r1_tarski(k1_relat_1(sK5),X0) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_3304]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_3307,plain,
% 7.25/1.61      ( k1_relat_1(sK5) != k1_xboole_0
% 7.25/1.61      | k1_xboole_0 != k1_xboole_0
% 7.25/1.61      | r1_tarski(k1_relat_1(sK5),k1_xboole_0) = iProver_top
% 7.25/1.61      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_3305]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_28,plain,
% 7.25/1.61      ( ~ v1_funct_2(X0,X1,X2)
% 7.25/1.61      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.25/1.61      | ~ v1_funct_1(X0)
% 7.25/1.61      | ~ v1_xboole_0(X0)
% 7.25/1.61      | v1_xboole_0(X1)
% 7.25/1.61      | v1_xboole_0(X2) ),
% 7.25/1.61      inference(cnf_transformation,[],[f100]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_20,plain,
% 7.25/1.61      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 7.25/1.61      inference(cnf_transformation,[],[f92]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_254,plain,
% 7.25/1.61      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.25/1.61      | ~ v1_funct_2(X0,X1,X2)
% 7.25/1.61      | ~ v1_xboole_0(X0)
% 7.25/1.61      | v1_xboole_0(X1)
% 7.25/1.61      | v1_xboole_0(X2) ),
% 7.25/1.61      inference(global_propositional_subsumption,
% 7.25/1.61                [status(thm)],
% 7.25/1.61                [c_28,c_20]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_255,plain,
% 7.25/1.61      ( ~ v1_funct_2(X0,X1,X2)
% 7.25/1.61      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.25/1.61      | ~ v1_xboole_0(X0)
% 7.25/1.61      | v1_xboole_0(X1)
% 7.25/1.61      | v1_xboole_0(X2) ),
% 7.25/1.61      inference(renaming,[status(thm)],[c_254]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2378,plain,
% 7.25/1.61      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.25/1.61      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.25/1.61      | v1_xboole_0(X0) != iProver_top
% 7.25/1.61      | v1_xboole_0(X2) = iProver_top
% 7.25/1.61      | v1_xboole_0(X1) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_255]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_3457,plain,
% 7.25/1.61      ( v1_funct_2(sK4,sK2,sK3) != iProver_top
% 7.25/1.61      | v1_xboole_0(sK3) = iProver_top
% 7.25/1.61      | v1_xboole_0(sK2) = iProver_top
% 7.25/1.61      | v1_xboole_0(sK4) != iProver_top ),
% 7.25/1.61      inference(superposition,[status(thm)],[c_2382,c_2378]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_18,plain,
% 7.25/1.61      ( ~ v1_relat_1(X0)
% 7.25/1.61      | v1_xboole_0(X0)
% 7.25/1.61      | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 7.25/1.61      inference(cnf_transformation,[],[f90]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_3688,plain,
% 7.25/1.61      ( ~ v1_relat_1(sK4)
% 7.25/1.61      | ~ v1_xboole_0(k2_relat_1(sK4))
% 7.25/1.61      | v1_xboole_0(sK4) ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_18]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_3689,plain,
% 7.25/1.61      ( v1_relat_1(sK4) != iProver_top
% 7.25/1.61      | v1_xboole_0(k2_relat_1(sK4)) != iProver_top
% 7.25/1.61      | v1_xboole_0(sK4) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_3688]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_8,plain,
% 7.25/1.61      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.25/1.61      | ~ v1_xboole_0(X1)
% 7.25/1.61      | v1_xboole_0(X0) ),
% 7.25/1.61      inference(cnf_transformation,[],[f80]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_10,plain,
% 7.25/1.61      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.25/1.61      inference(cnf_transformation,[],[f83]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_340,plain,
% 7.25/1.61      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.25/1.61      inference(prop_impl,[status(thm)],[c_10]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_341,plain,
% 7.25/1.61      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.25/1.61      inference(renaming,[status(thm)],[c_340]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_414,plain,
% 7.25/1.61      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 7.25/1.61      inference(bin_hyper_res,[status(thm)],[c_8,c_341]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_5548,plain,
% 7.25/1.61      ( ~ r1_tarski(k2_relat_1(sK4),X0)
% 7.25/1.61      | ~ v1_xboole_0(X0)
% 7.25/1.61      | v1_xboole_0(k2_relat_1(sK4)) ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_414]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_5552,plain,
% 7.25/1.61      ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 7.25/1.61      | v1_xboole_0(X0) != iProver_top
% 7.25/1.61      | v1_xboole_0(k2_relat_1(sK4)) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_5548]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_5554,plain,
% 7.25/1.61      ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
% 7.25/1.61      | v1_xboole_0(k2_relat_1(sK4)) = iProver_top
% 7.25/1.61      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_5552]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_15,plain,
% 7.25/1.61      ( v5_relat_1(X0,X1)
% 7.25/1.61      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.25/1.61      | ~ v1_relat_1(X0) ),
% 7.25/1.61      inference(cnf_transformation,[],[f88]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2405,plain,
% 7.25/1.61      ( v5_relat_1(X0,X1) = iProver_top
% 7.25/1.61      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.25/1.61      | v1_relat_1(X0) != iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_6228,plain,
% 7.25/1.61      ( v5_relat_1(sK4,k1_relat_1(sK5)) = iProver_top
% 7.25/1.61      | v1_relat_1(sK4) != iProver_top ),
% 7.25/1.61      inference(superposition,[status(thm)],[c_5707,c_2405]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_10700,plain,
% 7.25/1.61      ( v5_relat_1(sK4,k1_relat_1(sK5)) = iProver_top ),
% 7.25/1.61      inference(global_propositional_subsumption,
% 7.25/1.61                [status(thm)],
% 7.25/1.61                [c_6228,c_52,c_2775]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_19,plain,
% 7.25/1.61      ( ~ v5_relat_1(X0,X1)
% 7.25/1.61      | v5_relat_1(X0,X2)
% 7.25/1.61      | ~ r1_tarski(X1,X2)
% 7.25/1.61      | ~ v1_relat_1(X0) ),
% 7.25/1.61      inference(cnf_transformation,[],[f91]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2401,plain,
% 7.25/1.61      ( v5_relat_1(X0,X1) != iProver_top
% 7.25/1.61      | v5_relat_1(X0,X2) = iProver_top
% 7.25/1.61      | r1_tarski(X1,X2) != iProver_top
% 7.25/1.61      | v1_relat_1(X0) != iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_10705,plain,
% 7.25/1.61      ( v5_relat_1(sK4,X0) = iProver_top
% 7.25/1.61      | r1_tarski(k1_relat_1(sK5),X0) != iProver_top
% 7.25/1.61      | v1_relat_1(sK4) != iProver_top ),
% 7.25/1.61      inference(superposition,[status(thm)],[c_10700,c_2401]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_10707,plain,
% 7.25/1.61      ( v5_relat_1(sK4,k1_xboole_0) = iProver_top
% 7.25/1.61      | r1_tarski(k1_relat_1(sK5),k1_xboole_0) != iProver_top
% 7.25/1.61      | v1_relat_1(sK4) != iProver_top ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_10705]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_25462,plain,
% 7.25/1.61      ( k7_partfun1(X0,sK5,k1_funct_1(sK4,X1)) = k1_funct_1(sK5,k1_funct_1(sK4,X1))
% 7.25/1.61      | v5_relat_1(sK5,X0) != iProver_top
% 7.25/1.61      | r2_hidden(X1,sK2) != iProver_top ),
% 7.25/1.61      inference(global_propositional_subsumption,
% 7.25/1.61                [status(thm)],
% 7.25/1.61                [c_25426,c_49,c_51,c_52,c_53,c_54,c_40,c_133,c_134,c_138,
% 7.25/1.61                 c_143,c_2747,c_2772,c_2775,c_3008,c_3307,c_3457,c_3689,
% 7.25/1.61                 c_5554,c_10707]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_25471,plain,
% 7.25/1.61      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,X0)) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
% 7.25/1.61      | r2_hidden(X0,sK2) != iProver_top ),
% 7.25/1.61      inference(superposition,[status(thm)],[c_4316,c_25462]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_25619,plain,
% 7.25/1.61      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
% 7.25/1.61      inference(superposition,[status(thm)],[c_5806,c_25471]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_31,plain,
% 7.25/1.61      ( ~ v1_funct_2(X0,X1,X2)
% 7.25/1.61      | ~ m1_subset_1(X3,X1)
% 7.25/1.61      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 7.25/1.61      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.25/1.61      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 7.25/1.61      | ~ v1_funct_1(X4)
% 7.25/1.61      | ~ v1_funct_1(X0)
% 7.25/1.61      | v1_xboole_0(X2)
% 7.25/1.61      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 7.25/1.61      | k1_xboole_0 = X1 ),
% 7.25/1.61      inference(cnf_transformation,[],[f103]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2392,plain,
% 7.25/1.61      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 7.25/1.61      | k1_xboole_0 = X0
% 7.25/1.61      | v1_funct_2(X3,X0,X1) != iProver_top
% 7.25/1.61      | m1_subset_1(X5,X0) != iProver_top
% 7.25/1.61      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.25/1.61      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.25/1.61      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 7.25/1.61      | v1_funct_1(X3) != iProver_top
% 7.25/1.61      | v1_funct_1(X4) != iProver_top
% 7.25/1.61      | v1_xboole_0(X1) = iProver_top ),
% 7.25/1.61      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_8268,plain,
% 7.25/1.61      ( k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))
% 7.25/1.61      | sK2 = k1_xboole_0
% 7.25/1.61      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 7.25/1.61      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
% 7.25/1.61      | m1_subset_1(X2,sK2) != iProver_top
% 7.25/1.61      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 7.25/1.61      | r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
% 7.25/1.61      | v1_funct_1(X1) != iProver_top
% 7.25/1.61      | v1_funct_1(sK4) != iProver_top
% 7.25/1.61      | v1_xboole_0(sK3) = iProver_top ),
% 7.25/1.61      inference(superposition,[status(thm)],[c_4342,c_2392]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_1434,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2834,plain,
% 7.25/1.61      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_1434]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_2835,plain,
% 7.25/1.61      ( sK2 != k1_xboole_0
% 7.25/1.61      | k1_xboole_0 = sK2
% 7.25/1.61      | k1_xboole_0 != k1_xboole_0 ),
% 7.25/1.61      inference(instantiation,[status(thm)],[c_2834]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_9120,plain,
% 7.25/1.61      ( m1_subset_1(X2,sK2) != iProver_top
% 7.25/1.61      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
% 7.25/1.61      | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))
% 7.25/1.61      | r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
% 7.25/1.61      | v1_funct_1(X1) != iProver_top ),
% 7.25/1.61      inference(global_propositional_subsumption,
% 7.25/1.61                [status(thm)],
% 7.25/1.61                [c_8268,c_49,c_50,c_51,c_52,c_40,c_133,c_138,c_2835]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_9121,plain,
% 7.25/1.61      ( k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))
% 7.25/1.61      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
% 7.25/1.61      | m1_subset_1(X2,sK2) != iProver_top
% 7.25/1.61      | r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
% 7.25/1.61      | v1_funct_1(X1) != iProver_top ),
% 7.25/1.61      inference(renaming,[status(thm)],[c_9120]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_9132,plain,
% 7.25/1.61      ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
% 7.25/1.61      | m1_subset_1(X0,sK2) != iProver_top
% 7.25/1.61      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.25/1.61      | r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
% 7.25/1.61      | v1_funct_1(sK5) != iProver_top ),
% 7.25/1.61      inference(superposition,[status(thm)],[c_5103,c_9121]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_9162,plain,
% 7.25/1.61      ( m1_subset_1(X0,sK2) != iProver_top
% 7.25/1.61      | k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0)) ),
% 7.25/1.61      inference(global_propositional_subsumption,
% 7.25/1.61                [status(thm)],
% 7.25/1.61                [c_9132,c_53,c_54,c_5707]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_9163,plain,
% 7.25/1.61      ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
% 7.25/1.61      | m1_subset_1(X0,sK2) != iProver_top ),
% 7.25/1.61      inference(renaming,[status(thm)],[c_9162]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_9171,plain,
% 7.25/1.61      ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
% 7.25/1.61      inference(superposition,[status(thm)],[c_2385,c_9163]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_39,negated_conjecture,
% 7.25/1.61      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
% 7.25/1.61      inference(cnf_transformation,[],[f120]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(c_9968,plain,
% 7.25/1.61      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
% 7.25/1.61      inference(demodulation,[status(thm)],[c_9171,c_39]) ).
% 7.25/1.61  
% 7.25/1.61  cnf(contradiction,plain,
% 7.25/1.61      ( $false ),
% 7.25/1.61      inference(minisat,[status(thm)],[c_25619,c_9968]) ).
% 7.25/1.61  
% 7.25/1.61  
% 7.25/1.61  % SZS output end CNFRefutation for theBenchmark.p
% 7.25/1.61  
% 7.25/1.61  ------                               Statistics
% 7.25/1.61  
% 7.25/1.61  ------ General
% 7.25/1.61  
% 7.25/1.61  abstr_ref_over_cycles:                  0
% 7.25/1.61  abstr_ref_under_cycles:                 0
% 7.25/1.61  gc_basic_clause_elim:                   0
% 7.25/1.61  forced_gc_time:                         0
% 7.25/1.61  parsing_time:                           0.013
% 7.25/1.61  unif_index_cands_time:                  0.
% 7.25/1.61  unif_index_add_time:                    0.
% 7.25/1.61  orderings_time:                         0.
% 7.25/1.61  out_proof_time:                         0.014
% 7.25/1.61  total_time:                             0.667
% 7.25/1.61  num_of_symbols:                         57
% 7.25/1.61  num_of_terms:                           20419
% 7.25/1.61  
% 7.25/1.61  ------ Preprocessing
% 7.25/1.61  
% 7.25/1.61  num_of_splits:                          0
% 7.25/1.61  num_of_split_atoms:                     0
% 7.25/1.61  num_of_reused_defs:                     0
% 7.25/1.61  num_eq_ax_congr_red:                    21
% 7.25/1.61  num_of_sem_filtered_clauses:            1
% 7.25/1.61  num_of_subtypes:                        0
% 7.25/1.61  monotx_restored_types:                  0
% 7.25/1.61  sat_num_of_epr_types:                   0
% 7.25/1.61  sat_num_of_non_cyclic_types:            0
% 7.25/1.61  sat_guarded_non_collapsed_types:        0
% 7.25/1.61  num_pure_diseq_elim:                    0
% 7.25/1.61  simp_replaced_by:                       0
% 7.25/1.61  res_preprocessed:                       209
% 7.25/1.61  prep_upred:                             0
% 7.25/1.61  prep_unflattend:                        16
% 7.25/1.61  smt_new_axioms:                         0
% 7.25/1.61  pred_elim_cands:                        9
% 7.25/1.61  pred_elim:                              0
% 7.25/1.61  pred_elim_cl:                           0
% 7.25/1.61  pred_elim_cycles:                       2
% 7.25/1.61  merged_defs:                            8
% 7.25/1.61  merged_defs_ncl:                        0
% 7.25/1.61  bin_hyper_res:                          9
% 7.25/1.61  prep_cycles:                            4
% 7.25/1.61  pred_elim_time:                         0.015
% 7.25/1.61  splitting_time:                         0.
% 7.25/1.61  sem_filter_time:                        0.
% 7.25/1.61  monotx_time:                            0.001
% 7.25/1.61  subtype_inf_time:                       0.
% 7.25/1.61  
% 7.25/1.61  ------ Problem properties
% 7.25/1.61  
% 7.25/1.61  clauses:                                44
% 7.25/1.61  conjectures:                            10
% 7.25/1.61  epr:                                    16
% 7.25/1.61  horn:                                   38
% 7.25/1.61  ground:                                 11
% 7.25/1.61  unary:                                  15
% 7.25/1.61  binary:                                 11
% 7.25/1.61  lits:                                   117
% 7.25/1.61  lits_eq:                                12
% 7.25/1.61  fd_pure:                                0
% 7.25/1.61  fd_pseudo:                              0
% 7.25/1.61  fd_cond:                                5
% 7.25/1.61  fd_pseudo_cond:                         1
% 7.25/1.61  ac_symbols:                             0
% 7.25/1.61  
% 7.25/1.61  ------ Propositional Solver
% 7.25/1.61  
% 7.25/1.61  prop_solver_calls:                      29
% 7.25/1.61  prop_fast_solver_calls:                 2402
% 7.25/1.61  smt_solver_calls:                       0
% 7.25/1.61  smt_fast_solver_calls:                  0
% 7.25/1.61  prop_num_of_clauses:                    9162
% 7.25/1.61  prop_preprocess_simplified:             21633
% 7.25/1.61  prop_fo_subsumed:                       131
% 7.25/1.61  prop_solver_time:                       0.
% 7.25/1.61  smt_solver_time:                        0.
% 7.25/1.61  smt_fast_solver_time:                   0.
% 7.25/1.61  prop_fast_solver_time:                  0.
% 7.25/1.61  prop_unsat_core_time:                   0.001
% 7.25/1.61  
% 7.25/1.61  ------ QBF
% 7.25/1.61  
% 7.25/1.61  qbf_q_res:                              0
% 7.25/1.61  qbf_num_tautologies:                    0
% 7.25/1.61  qbf_prep_cycles:                        0
% 7.25/1.61  
% 7.25/1.61  ------ BMC1
% 7.25/1.61  
% 7.25/1.61  bmc1_current_bound:                     -1
% 7.25/1.61  bmc1_last_solved_bound:                 -1
% 7.25/1.61  bmc1_unsat_core_size:                   -1
% 7.25/1.61  bmc1_unsat_core_parents_size:           -1
% 7.25/1.61  bmc1_merge_next_fun:                    0
% 7.25/1.61  bmc1_unsat_core_clauses_time:           0.
% 7.25/1.61  
% 7.25/1.61  ------ Instantiation
% 7.25/1.61  
% 7.25/1.61  inst_num_of_clauses:                    2461
% 7.25/1.61  inst_num_in_passive:                    905
% 7.25/1.61  inst_num_in_active:                     1165
% 7.25/1.61  inst_num_in_unprocessed:                396
% 7.25/1.61  inst_num_of_loops:                      1300
% 7.25/1.61  inst_num_of_learning_restarts:          0
% 7.25/1.61  inst_num_moves_active_passive:          133
% 7.25/1.61  inst_lit_activity:                      0
% 7.25/1.61  inst_lit_activity_moves:                0
% 7.25/1.61  inst_num_tautologies:                   0
% 7.25/1.61  inst_num_prop_implied:                  0
% 7.25/1.61  inst_num_existing_simplified:           0
% 7.25/1.61  inst_num_eq_res_simplified:             0
% 7.25/1.61  inst_num_child_elim:                    0
% 7.25/1.61  inst_num_of_dismatching_blockings:      1197
% 7.25/1.61  inst_num_of_non_proper_insts:           3115
% 7.25/1.61  inst_num_of_duplicates:                 0
% 7.25/1.61  inst_inst_num_from_inst_to_res:         0
% 7.25/1.61  inst_dismatching_checking_time:         0.
% 7.25/1.61  
% 7.25/1.61  ------ Resolution
% 7.25/1.61  
% 7.25/1.61  res_num_of_clauses:                     0
% 7.25/1.61  res_num_in_passive:                     0
% 7.25/1.61  res_num_in_active:                      0
% 7.25/1.61  res_num_of_loops:                       213
% 7.25/1.61  res_forward_subset_subsumed:            215
% 7.25/1.61  res_backward_subset_subsumed:           10
% 7.25/1.61  res_forward_subsumed:                   0
% 7.25/1.61  res_backward_subsumed:                  0
% 7.25/1.61  res_forward_subsumption_resolution:     0
% 7.25/1.61  res_backward_subsumption_resolution:    0
% 7.25/1.61  res_clause_to_clause_subsumption:       1286
% 7.25/1.61  res_orphan_elimination:                 0
% 7.25/1.61  res_tautology_del:                      174
% 7.25/1.61  res_num_eq_res_simplified:              0
% 7.25/1.61  res_num_sel_changes:                    0
% 7.25/1.61  res_moves_from_active_to_pass:          0
% 7.25/1.61  
% 7.25/1.61  ------ Superposition
% 7.25/1.61  
% 7.25/1.61  sup_time_total:                         0.
% 7.25/1.61  sup_time_generating:                    0.
% 7.25/1.61  sup_time_sim_full:                      0.
% 7.25/1.61  sup_time_sim_immed:                     0.
% 7.25/1.61  
% 7.25/1.61  sup_num_of_clauses:                     402
% 7.25/1.61  sup_num_in_active:                      253
% 7.25/1.61  sup_num_in_passive:                     149
% 7.25/1.61  sup_num_of_loops:                       258
% 7.25/1.61  sup_fw_superposition:                   356
% 7.25/1.61  sup_bw_superposition:                   198
% 7.25/1.61  sup_immediate_simplified:               79
% 7.25/1.61  sup_given_eliminated:                   0
% 7.25/1.61  comparisons_done:                       0
% 7.25/1.61  comparisons_avoided:                    18
% 7.25/1.61  
% 7.25/1.61  ------ Simplifications
% 7.25/1.61  
% 7.25/1.61  
% 7.25/1.61  sim_fw_subset_subsumed:                 48
% 7.25/1.61  sim_bw_subset_subsumed:                 4
% 7.25/1.61  sim_fw_subsumed:                        10
% 7.25/1.61  sim_bw_subsumed:                        0
% 7.25/1.61  sim_fw_subsumption_res:                 13
% 7.25/1.61  sim_bw_subsumption_res:                 0
% 7.25/1.61  sim_tautology_del:                      9
% 7.25/1.61  sim_eq_tautology_del:                   11
% 7.25/1.61  sim_eq_res_simp:                        0
% 7.25/1.61  sim_fw_demodulated:                     5
% 7.25/1.61  sim_bw_demodulated:                     6
% 7.25/1.61  sim_light_normalised:                   27
% 7.25/1.61  sim_joinable_taut:                      0
% 7.25/1.61  sim_joinable_simp:                      0
% 7.25/1.61  sim_ac_normalised:                      0
% 7.25/1.61  sim_smt_subsumption:                    0
% 7.25/1.61  
%------------------------------------------------------------------------------

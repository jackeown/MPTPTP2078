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
% DateTime   : Thu Dec  3 12:09:44 EST 2020

% Result     : Theorem 7.91s
% Output     : CNFRefutation 7.91s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 645 expanded)
%              Number of clauses        :  109 ( 177 expanded)
%              Number of leaves         :   26 ( 219 expanded)
%              Depth                    :   23
%              Number of atoms          :  674 (4830 expanded)
%              Number of equality atoms :  269 (1329 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,conjecture,(
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

fof(f26,negated_conjecture,(
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
    inference(negated_conjecture,[],[f25])).

fof(f57,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK11) != k7_partfun1(X0,X4,k1_funct_1(X3,sK11))
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK11,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
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
            ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK10),X5) != k7_partfun1(X0,sK10,k1_funct_1(X3,X5))
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK10))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
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
                ( k1_funct_1(k8_funct_2(X1,X2,X0,sK9,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK9,X5))
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK9),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK9,X1,X2)
        & v1_funct_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,
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
                  ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,X3,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK7
                  & r1_tarski(k2_relset_1(sK7,sK8,X3),k1_relset_1(sK8,sK6,X4))
                  & m1_subset_1(X5,sK7) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
          & v1_funct_2(X3,sK7,sK8)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,
    ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11))
    & k1_xboole_0 != sK7
    & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
    & m1_subset_1(sK11,sK7)
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
    & v1_funct_1(sK10)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    & v1_funct_2(sK9,sK7,sK8)
    & v1_funct_1(sK9)
    & ~ v1_xboole_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f58,f82,f81,f80,f79])).

fof(f139,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) ),
    inference(cnf_transformation,[],[f83])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f140,plain,(
    m1_subset_1(sK11,sK7) ),
    inference(cnf_transformation,[],[f83])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f142,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f83])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f87,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f141,plain,(
    r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) ),
    inference(cnf_transformation,[],[f83])).

fof(f137,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(cnf_transformation,[],[f83])).

fof(f24,axiom,(
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

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f24])).

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
    inference(flattening,[],[f55])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f134,plain,(
    ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f83])).

fof(f135,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f83])).

fof(f136,plain,(
    v1_funct_2(sK9,sK7,sK8) ),
    inference(cnf_transformation,[],[f83])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f53])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f138,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f83])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f22,axiom,(
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

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f22])).

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
    inference(flattening,[],[f51])).

fof(f126,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f67])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f147,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f96])).

fof(f143,plain,(
    k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) ),
    inference(cnf_transformation,[],[f83])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f20,axiom,(
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

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f20])).

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
    inference(flattening,[],[f47])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f103,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f146,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f97])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f63])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f8,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f98,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_54,negated_conjecture,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_1922,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_35,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1934,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_6326,plain,
    ( v5_relat_1(sK10,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1922,c_1934])).

cnf(c_53,negated_conjecture,
    ( m1_subset_1(sK11,sK7) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_1923,plain,
    ( m1_subset_1(sK11,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1952,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9044,plain,
    ( r2_hidden(sK11,sK7) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1923,c_1952])).

cnf(c_51,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f142])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2384,plain,
    ( ~ v1_xboole_0(sK7)
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2385,plain,
    ( k1_xboole_0 = sK7
    | v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2384])).

cnf(c_2911,plain,
    ( r2_hidden(sK11,sK7)
    | v1_xboole_0(sK7) ),
    inference(resolution,[status(thm)],[c_15,c_53])).

cnf(c_2912,plain,
    ( r2_hidden(sK11,sK7) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2911])).

cnf(c_9277,plain,
    ( r2_hidden(sK11,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9044,c_51,c_2385,c_2912])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1933,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_7878,plain,
    ( k1_relset_1(sK8,sK6,sK10) = k1_relat_1(sK10) ),
    inference(superposition,[status(thm)],[c_1922,c_1933])).

cnf(c_52,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_1924,plain,
    ( r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_56,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_1920,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_45,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f132])).

cnf(c_1927,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_4073,plain,
    ( sK8 = k1_xboole_0
    | v1_funct_2(sK9,sK7,sK8) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK7,sK8,sK9),X0) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1920,c_1927])).

cnf(c_59,negated_conjecture,
    ( ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_58,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_61,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_57,negated_conjecture,
    ( v1_funct_2(sK9,sK7,sK8) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_62,plain,
    ( v1_funct_2(sK9,sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_893,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2437,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK8)
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_893])).

cnf(c_2439,plain,
    ( v1_xboole_0(sK8)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK8 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2437])).

cnf(c_4618,plain,
    ( r1_tarski(k2_relset_1(sK7,sK8,sK9),X0) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4073,c_59,c_61,c_62,c_2,c_2439])).

cnf(c_4619,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK7,sK8,sK9),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4618])).

cnf(c_4627,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_relset_1(sK8,sK6,sK10)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1924,c_4619])).

cnf(c_43,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1929,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_5026,plain,
    ( k1_relset_1(sK8,sK6,sK10) = k1_xboole_0
    | v1_funct_2(sK9,sK7,k1_relset_1(sK8,sK6,sK10)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(k1_funct_1(sK9,X0),k1_relset_1(sK8,sK6,sK10)) = iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_4627,c_1929])).

cnf(c_63,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_67,plain,
    ( r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_47,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_2571,plain,
    ( v1_funct_2(sK9,sK7,X0)
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ r1_tarski(k2_relset_1(sK7,sK8,sK9),X0)
    | ~ v1_funct_1(sK9)
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_2818,plain,
    ( v1_funct_2(sK9,sK7,k1_relset_1(sK8,sK6,sK10))
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
    | ~ v1_funct_1(sK9)
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_2571])).

cnf(c_2819,plain,
    ( k1_xboole_0 = sK8
    | v1_funct_2(sK9,sK7,k1_relset_1(sK8,sK6,sK10)) = iProver_top
    | v1_funct_2(sK9,sK7,sK8) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2818])).

cnf(c_892,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2722,plain,
    ( X0 != X1
    | sK8 != X1
    | sK8 = X0 ),
    inference(instantiation,[status(thm)],[c_892])).

cnf(c_3430,plain,
    ( X0 != sK8
    | sK8 = X0
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_2722])).

cnf(c_3432,plain,
    ( sK8 != sK8
    | sK8 = k1_xboole_0
    | k1_xboole_0 != sK8 ),
    inference(instantiation,[status(thm)],[c_3430])).

cnf(c_891,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3431,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_891])).

cnf(c_6036,plain,
    ( r2_hidden(k1_funct_1(sK9,X0),k1_relset_1(sK8,sK6,sK10)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | k1_relset_1(sK8,sK6,sK10) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5026,c_59,c_61,c_62,c_63,c_67,c_2,c_2439,c_2819,c_3432,c_3431])).

cnf(c_6037,plain,
    ( k1_relset_1(sK8,sK6,sK10) = k1_xboole_0
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(k1_funct_1(sK9,X0),k1_relset_1(sK8,sK6,sK10)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6036])).

cnf(c_8066,plain,
    ( k1_relat_1(sK10) = k1_xboole_0
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(k1_funct_1(sK9,X0),k1_relat_1(sK10)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7878,c_6037])).

cnf(c_41,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1931,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | v5_relat_1(X1,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_14696,plain,
    ( k7_partfun1(X0,sK10,k1_funct_1(sK9,X1)) = k1_funct_1(sK10,k1_funct_1(sK9,X1))
    | k1_relat_1(sK10) = k1_xboole_0
    | v5_relat_1(sK10,X0) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_8066,c_1931])).

cnf(c_55,negated_conjecture,
    ( v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_64,plain,
    ( v1_funct_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_65,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2417,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
    | v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_2418,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) != iProver_top
    | v1_relat_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2417])).

cnf(c_32317,plain,
    ( k7_partfun1(X0,sK10,k1_funct_1(sK9,X1)) = k1_funct_1(sK10,k1_funct_1(sK9,X1))
    | k1_relat_1(sK10) = k1_xboole_0
    | v5_relat_1(sK10,X0) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14696,c_64,c_65,c_2418])).

cnf(c_32334,plain,
    ( k7_partfun1(X0,sK10,k1_funct_1(sK9,sK11)) = k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | k1_relat_1(sK10) = k1_xboole_0
    | v5_relat_1(sK10,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9277,c_32317])).

cnf(c_32673,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) = k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | k1_relat_1(sK10) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6326,c_32334])).

cnf(c_42,plain,
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
    inference(cnf_transformation,[],[f126])).

cnf(c_1930,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_6168,plain,
    ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),X0) = k1_funct_1(sK10,k1_funct_1(sK9,X0))
    | sK7 = k1_xboole_0
    | v1_funct_2(sK9,sK7,sK8) != iProver_top
    | m1_subset_1(X0,sK7) != iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1924,c_1930])).

cnf(c_60,plain,
    ( v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_13,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_154,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f147])).

cnf(c_155,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2489,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_892])).

cnf(c_2490,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2489])).

cnf(c_7428,plain,
    ( m1_subset_1(X0,sK7) != iProver_top
    | k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),X0) = k1_funct_1(sK10,k1_funct_1(sK9,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6168,c_60,c_61,c_62,c_63,c_64,c_65,c_51,c_154,c_155,c_2490])).

cnf(c_7429,plain,
    ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),X0) = k1_funct_1(sK10,k1_funct_1(sK9,X0))
    | m1_subset_1(X0,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_7428])).

cnf(c_7436,plain,
    ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) = k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
    inference(superposition,[status(thm)],[c_1923,c_7429])).

cnf(c_50,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_7438,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
    inference(demodulation,[status(thm)],[c_7436,c_50])).

cnf(c_32674,plain,
    ( k1_relat_1(sK10) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32673,c_7438])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1950,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4636,plain,
    ( r1_tarski(sK9,k2_zfmisc_1(sK7,k1_relset_1(sK8,sK6,sK10))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4627,c_1950])).

cnf(c_8067,plain,
    ( r1_tarski(sK9,k2_zfmisc_1(sK7,k1_relat_1(sK10))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7878,c_4636])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1954,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_10404,plain,
    ( r1_xboole_0(sK9,k2_zfmisc_1(sK7,k1_relat_1(sK10))) != iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_8067,c_1954])).

cnf(c_39,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_19,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_521,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39,c_19])).

cnf(c_522,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(renaming,[status(thm)],[c_521])).

cnf(c_1916,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_2511,plain,
    ( v1_funct_2(sK9,sK7,sK8) != iProver_top
    | v1_xboole_0(sK9) != iProver_top
    | v1_xboole_0(sK8) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1920,c_1916])).

cnf(c_18556,plain,
    ( r1_xboole_0(sK9,k2_zfmisc_1(sK7,k1_relat_1(sK10))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10404,c_60,c_62,c_51,c_2385,c_2511])).

cnf(c_32683,plain,
    ( r1_xboole_0(sK9,k2_zfmisc_1(sK7,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_32674,c_18556])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f146])).

cnf(c_32734,plain,
    ( r1_xboole_0(sK9,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_32683,c_11])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1958,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1953,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3195,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1953])).

cnf(c_5468,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1958,c_3195])).

cnf(c_33075,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_32734,c_5468])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:42:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.91/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.91/1.50  
% 7.91/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.91/1.50  
% 7.91/1.50  ------  iProver source info
% 7.91/1.50  
% 7.91/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.91/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.91/1.50  git: non_committed_changes: false
% 7.91/1.50  git: last_make_outside_of_git: false
% 7.91/1.50  
% 7.91/1.50  ------ 
% 7.91/1.50  ------ Parsing...
% 7.91/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.91/1.50  
% 7.91/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.91/1.50  
% 7.91/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.91/1.50  
% 7.91/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.50  ------ Proving...
% 7.91/1.50  ------ Problem Properties 
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  clauses                                 54
% 7.91/1.50  conjectures                             10
% 7.91/1.50  EPR                                     15
% 7.91/1.50  Horn                                    41
% 7.91/1.50  unary                                   18
% 7.91/1.50  binary                                  13
% 7.91/1.50  lits                                    151
% 7.91/1.50  lits eq                                 27
% 7.91/1.50  fd_pure                                 0
% 7.91/1.50  fd_pseudo                               0
% 7.91/1.50  fd_cond                                 6
% 7.91/1.50  fd_pseudo_cond                          5
% 7.91/1.50  AC symbols                              0
% 7.91/1.50  
% 7.91/1.50  ------ Input Options Time Limit: Unbounded
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  ------ 
% 7.91/1.50  Current options:
% 7.91/1.50  ------ 
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  ------ Proving...
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  % SZS status Theorem for theBenchmark.p
% 7.91/1.50  
% 7.91/1.50   Resolution empty clause
% 7.91/1.50  
% 7.91/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.91/1.50  
% 7.91/1.50  fof(f25,conjecture,(
% 7.91/1.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 7.91/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f26,negated_conjecture,(
% 7.91/1.50    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 7.91/1.50    inference(negated_conjecture,[],[f25])).
% 7.91/1.50  
% 7.91/1.50  fof(f57,plain,(
% 7.91/1.50    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 7.91/1.50    inference(ennf_transformation,[],[f26])).
% 7.91/1.50  
% 7.91/1.50  fof(f58,plain,(
% 7.91/1.50    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 7.91/1.50    inference(flattening,[],[f57])).
% 7.91/1.50  
% 7.91/1.50  fof(f82,plain,(
% 7.91/1.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK11) != k7_partfun1(X0,X4,k1_funct_1(X3,sK11)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK11,X1))) )),
% 7.91/1.50    introduced(choice_axiom,[])).
% 7.91/1.50  
% 7.91/1.50  fof(f81,plain,(
% 7.91/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK10),X5) != k7_partfun1(X0,sK10,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK10)) & m1_subset_1(X5,X1)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK10))) )),
% 7.91/1.50    introduced(choice_axiom,[])).
% 7.91/1.50  
% 7.91/1.50  fof(f80,plain,(
% 7.91/1.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK9,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK9,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK9),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK9,X1,X2) & v1_funct_1(sK9))) )),
% 7.91/1.50    introduced(choice_axiom,[])).
% 7.91/1.50  
% 7.91/1.50  fof(f79,plain,(
% 7.91/1.50    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK7,sK8,sK6,X3,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,X3),k1_relset_1(sK8,sK6,X4)) & m1_subset_1(X5,sK7)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(X3,sK7,sK8) & v1_funct_1(X3)) & ~v1_xboole_0(sK8))),
% 7.91/1.50    introduced(choice_axiom,[])).
% 7.91/1.50  
% 7.91/1.50  fof(f83,plain,(
% 7.91/1.50    (((k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) & m1_subset_1(sK11,sK7)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) & v1_funct_1(sK10)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(sK9,sK7,sK8) & v1_funct_1(sK9)) & ~v1_xboole_0(sK8)),
% 7.91/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f58,f82,f81,f80,f79])).
% 7.91/1.50  
% 7.91/1.50  fof(f139,plain,(
% 7.91/1.50    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))),
% 7.91/1.50    inference(cnf_transformation,[],[f83])).
% 7.91/1.50  
% 7.91/1.50  fof(f17,axiom,(
% 7.91/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.91/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f28,plain,(
% 7.91/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.91/1.50    inference(pure_predicate_removal,[],[f17])).
% 7.91/1.50  
% 7.91/1.50  fof(f44,plain,(
% 7.91/1.50    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.91/1.50    inference(ennf_transformation,[],[f28])).
% 7.91/1.50  
% 7.91/1.50  fof(f119,plain,(
% 7.91/1.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.91/1.50    inference(cnf_transformation,[],[f44])).
% 7.91/1.50  
% 7.91/1.50  fof(f140,plain,(
% 7.91/1.50    m1_subset_1(sK11,sK7)),
% 7.91/1.50    inference(cnf_transformation,[],[f83])).
% 7.91/1.50  
% 7.91/1.50  fof(f9,axiom,(
% 7.91/1.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.91/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f33,plain,(
% 7.91/1.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.91/1.50    inference(ennf_transformation,[],[f9])).
% 7.91/1.50  
% 7.91/1.50  fof(f34,plain,(
% 7.91/1.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.91/1.50    inference(flattening,[],[f33])).
% 7.91/1.50  
% 7.91/1.50  fof(f99,plain,(
% 7.91/1.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f34])).
% 7.91/1.50  
% 7.91/1.50  fof(f142,plain,(
% 7.91/1.50    k1_xboole_0 != sK7),
% 7.91/1.50    inference(cnf_transformation,[],[f83])).
% 7.91/1.50  
% 7.91/1.50  fof(f3,axiom,(
% 7.91/1.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.91/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f29,plain,(
% 7.91/1.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.91/1.50    inference(ennf_transformation,[],[f3])).
% 7.91/1.50  
% 7.91/1.50  fof(f87,plain,(
% 7.91/1.50    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f29])).
% 7.91/1.50  
% 7.91/1.50  fof(f18,axiom,(
% 7.91/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.91/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f45,plain,(
% 7.91/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.91/1.50    inference(ennf_transformation,[],[f18])).
% 7.91/1.50  
% 7.91/1.50  fof(f120,plain,(
% 7.91/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.91/1.50    inference(cnf_transformation,[],[f45])).
% 7.91/1.50  
% 7.91/1.50  fof(f141,plain,(
% 7.91/1.50    r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))),
% 7.91/1.50    inference(cnf_transformation,[],[f83])).
% 7.91/1.50  
% 7.91/1.50  fof(f137,plain,(
% 7.91/1.50    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))),
% 7.91/1.50    inference(cnf_transformation,[],[f83])).
% 7.91/1.50  
% 7.91/1.50  fof(f24,axiom,(
% 7.91/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.91/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f55,plain,(
% 7.91/1.50    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.91/1.50    inference(ennf_transformation,[],[f24])).
% 7.91/1.50  
% 7.91/1.50  fof(f56,plain,(
% 7.91/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.91/1.50    inference(flattening,[],[f55])).
% 7.91/1.50  
% 7.91/1.50  fof(f132,plain,(
% 7.91/1.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f56])).
% 7.91/1.50  
% 7.91/1.50  fof(f134,plain,(
% 7.91/1.50    ~v1_xboole_0(sK8)),
% 7.91/1.50    inference(cnf_transformation,[],[f83])).
% 7.91/1.50  
% 7.91/1.50  fof(f135,plain,(
% 7.91/1.50    v1_funct_1(sK9)),
% 7.91/1.50    inference(cnf_transformation,[],[f83])).
% 7.91/1.50  
% 7.91/1.50  fof(f136,plain,(
% 7.91/1.50    v1_funct_2(sK9,sK7,sK8)),
% 7.91/1.50    inference(cnf_transformation,[],[f83])).
% 7.91/1.50  
% 7.91/1.50  fof(f2,axiom,(
% 7.91/1.50    v1_xboole_0(k1_xboole_0)),
% 7.91/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f86,plain,(
% 7.91/1.50    v1_xboole_0(k1_xboole_0)),
% 7.91/1.50    inference(cnf_transformation,[],[f2])).
% 7.91/1.50  
% 7.91/1.50  fof(f23,axiom,(
% 7.91/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 7.91/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f53,plain,(
% 7.91/1.50    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.91/1.50    inference(ennf_transformation,[],[f23])).
% 7.91/1.50  
% 7.91/1.50  fof(f54,plain,(
% 7.91/1.50    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.91/1.50    inference(flattening,[],[f53])).
% 7.91/1.50  
% 7.91/1.50  fof(f127,plain,(
% 7.91/1.50    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f54])).
% 7.91/1.50  
% 7.91/1.50  fof(f130,plain,(
% 7.91/1.50    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f56])).
% 7.91/1.50  
% 7.91/1.50  fof(f21,axiom,(
% 7.91/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 7.91/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f49,plain,(
% 7.91/1.50    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.91/1.50    inference(ennf_transformation,[],[f21])).
% 7.91/1.50  
% 7.91/1.50  fof(f50,plain,(
% 7.91/1.50    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.91/1.50    inference(flattening,[],[f49])).
% 7.91/1.50  
% 7.91/1.50  fof(f125,plain,(
% 7.91/1.50    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f50])).
% 7.91/1.50  
% 7.91/1.50  fof(f138,plain,(
% 7.91/1.50    v1_funct_1(sK10)),
% 7.91/1.50    inference(cnf_transformation,[],[f83])).
% 7.91/1.50  
% 7.91/1.50  fof(f16,axiom,(
% 7.91/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.91/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f43,plain,(
% 7.91/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.91/1.50    inference(ennf_transformation,[],[f16])).
% 7.91/1.50  
% 7.91/1.50  fof(f118,plain,(
% 7.91/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.91/1.50    inference(cnf_transformation,[],[f43])).
% 7.91/1.50  
% 7.91/1.50  fof(f22,axiom,(
% 7.91/1.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 7.91/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f51,plain,(
% 7.91/1.50    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 7.91/1.50    inference(ennf_transformation,[],[f22])).
% 7.91/1.50  
% 7.91/1.50  fof(f52,plain,(
% 7.91/1.50    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 7.91/1.50    inference(flattening,[],[f51])).
% 7.91/1.50  
% 7.91/1.50  fof(f126,plain,(
% 7.91/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f52])).
% 7.91/1.50  
% 7.91/1.50  fof(f7,axiom,(
% 7.91/1.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.91/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f67,plain,(
% 7.91/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.91/1.50    inference(nnf_transformation,[],[f7])).
% 7.91/1.50  
% 7.91/1.50  fof(f68,plain,(
% 7.91/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.91/1.50    inference(flattening,[],[f67])).
% 7.91/1.50  
% 7.91/1.50  fof(f95,plain,(
% 7.91/1.50    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f68])).
% 7.91/1.50  
% 7.91/1.50  fof(f96,plain,(
% 7.91/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.91/1.50    inference(cnf_transformation,[],[f68])).
% 7.91/1.50  
% 7.91/1.50  fof(f147,plain,(
% 7.91/1.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.91/1.50    inference(equality_resolution,[],[f96])).
% 7.91/1.50  
% 7.91/1.50  fof(f143,plain,(
% 7.91/1.50    k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11))),
% 7.91/1.50    inference(cnf_transformation,[],[f83])).
% 7.91/1.50  
% 7.91/1.50  fof(f10,axiom,(
% 7.91/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.91/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f69,plain,(
% 7.91/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.91/1.50    inference(nnf_transformation,[],[f10])).
% 7.91/1.50  
% 7.91/1.50  fof(f100,plain,(
% 7.91/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.91/1.50    inference(cnf_transformation,[],[f69])).
% 7.91/1.50  
% 7.91/1.50  fof(f6,axiom,(
% 7.91/1.50    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 7.91/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f31,plain,(
% 7.91/1.50    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 7.91/1.50    inference(ennf_transformation,[],[f6])).
% 7.91/1.50  
% 7.91/1.50  fof(f32,plain,(
% 7.91/1.50    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 7.91/1.50    inference(flattening,[],[f31])).
% 7.91/1.50  
% 7.91/1.50  fof(f94,plain,(
% 7.91/1.50    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f32])).
% 7.91/1.50  
% 7.91/1.50  fof(f20,axiom,(
% 7.91/1.50    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 7.91/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f47,plain,(
% 7.91/1.50    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.91/1.50    inference(ennf_transformation,[],[f20])).
% 7.91/1.50  
% 7.91/1.50  fof(f48,plain,(
% 7.91/1.50    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.91/1.50    inference(flattening,[],[f47])).
% 7.91/1.50  
% 7.91/1.50  fof(f123,plain,(
% 7.91/1.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f48])).
% 7.91/1.50  
% 7.91/1.50  fof(f12,axiom,(
% 7.91/1.50    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 7.91/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f37,plain,(
% 7.91/1.50    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 7.91/1.50    inference(ennf_transformation,[],[f12])).
% 7.91/1.50  
% 7.91/1.50  fof(f103,plain,(
% 7.91/1.50    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f37])).
% 7.91/1.50  
% 7.91/1.50  fof(f97,plain,(
% 7.91/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.91/1.50    inference(cnf_transformation,[],[f68])).
% 7.91/1.50  
% 7.91/1.50  fof(f146,plain,(
% 7.91/1.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.91/1.50    inference(equality_resolution,[],[f97])).
% 7.91/1.50  
% 7.91/1.50  fof(f4,axiom,(
% 7.91/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.91/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f27,plain,(
% 7.91/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.91/1.50    inference(rectify,[],[f4])).
% 7.91/1.50  
% 7.91/1.50  fof(f30,plain,(
% 7.91/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.91/1.50    inference(ennf_transformation,[],[f27])).
% 7.91/1.50  
% 7.91/1.50  fof(f63,plain,(
% 7.91/1.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.91/1.50    introduced(choice_axiom,[])).
% 7.91/1.50  
% 7.91/1.50  fof(f64,plain,(
% 7.91/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.91/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f63])).
% 7.91/1.50  
% 7.91/1.50  fof(f89,plain,(
% 7.91/1.50    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f64])).
% 7.91/1.50  
% 7.91/1.50  fof(f8,axiom,(
% 7.91/1.50    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 7.91/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f98,plain,(
% 7.91/1.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 7.91/1.50    inference(cnf_transformation,[],[f8])).
% 7.91/1.50  
% 7.91/1.50  cnf(c_54,negated_conjecture,
% 7.91/1.50      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) ),
% 7.91/1.50      inference(cnf_transformation,[],[f139]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1922,plain,
% 7.91/1.50      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_35,plain,
% 7.91/1.50      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.91/1.50      inference(cnf_transformation,[],[f119]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1934,plain,
% 7.91/1.50      ( v5_relat_1(X0,X1) = iProver_top
% 7.91/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6326,plain,
% 7.91/1.50      ( v5_relat_1(sK10,sK6) = iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1922,c_1934]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_53,negated_conjecture,
% 7.91/1.50      ( m1_subset_1(sK11,sK7) ),
% 7.91/1.50      inference(cnf_transformation,[],[f140]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1923,plain,
% 7.91/1.50      ( m1_subset_1(sK11,sK7) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_15,plain,
% 7.91/1.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.91/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1952,plain,
% 7.91/1.50      ( m1_subset_1(X0,X1) != iProver_top
% 7.91/1.50      | r2_hidden(X0,X1) = iProver_top
% 7.91/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_9044,plain,
% 7.91/1.50      ( r2_hidden(sK11,sK7) = iProver_top | v1_xboole_0(sK7) = iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1923,c_1952]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_51,negated_conjecture,
% 7.91/1.50      ( k1_xboole_0 != sK7 ),
% 7.91/1.50      inference(cnf_transformation,[],[f142]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_3,plain,
% 7.91/1.50      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.91/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2384,plain,
% 7.91/1.50      ( ~ v1_xboole_0(sK7) | k1_xboole_0 = sK7 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2385,plain,
% 7.91/1.50      ( k1_xboole_0 = sK7 | v1_xboole_0(sK7) != iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_2384]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2911,plain,
% 7.91/1.50      ( r2_hidden(sK11,sK7) | v1_xboole_0(sK7) ),
% 7.91/1.50      inference(resolution,[status(thm)],[c_15,c_53]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2912,plain,
% 7.91/1.50      ( r2_hidden(sK11,sK7) = iProver_top | v1_xboole_0(sK7) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_2911]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_9277,plain,
% 7.91/1.50      ( r2_hidden(sK11,sK7) = iProver_top ),
% 7.91/1.50      inference(global_propositional_subsumption,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_9044,c_51,c_2385,c_2912]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_36,plain,
% 7.91/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.91/1.50      inference(cnf_transformation,[],[f120]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1933,plain,
% 7.91/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.91/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_7878,plain,
% 7.91/1.50      ( k1_relset_1(sK8,sK6,sK10) = k1_relat_1(sK10) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1922,c_1933]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_52,negated_conjecture,
% 7.91/1.50      ( r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) ),
% 7.91/1.50      inference(cnf_transformation,[],[f141]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1924,plain,
% 7.91/1.50      ( r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_56,negated_conjecture,
% 7.91/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
% 7.91/1.50      inference(cnf_transformation,[],[f137]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1920,plain,
% 7.91/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_45,plain,
% 7.91/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.91/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.91/1.50      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 7.91/1.50      | ~ v1_funct_1(X0)
% 7.91/1.50      | k1_xboole_0 = X2 ),
% 7.91/1.50      inference(cnf_transformation,[],[f132]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1927,plain,
% 7.91/1.50      ( k1_xboole_0 = X0
% 7.91/1.50      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.91/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.91/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 7.91/1.50      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 7.91/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4073,plain,
% 7.91/1.50      ( sK8 = k1_xboole_0
% 7.91/1.50      | v1_funct_2(sK9,sK7,sK8) != iProver_top
% 7.91/1.50      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) = iProver_top
% 7.91/1.50      | r1_tarski(k2_relset_1(sK7,sK8,sK9),X0) != iProver_top
% 7.91/1.50      | v1_funct_1(sK9) != iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1920,c_1927]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_59,negated_conjecture,
% 7.91/1.50      ( ~ v1_xboole_0(sK8) ),
% 7.91/1.50      inference(cnf_transformation,[],[f134]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_58,negated_conjecture,
% 7.91/1.50      ( v1_funct_1(sK9) ),
% 7.91/1.50      inference(cnf_transformation,[],[f135]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_61,plain,
% 7.91/1.50      ( v1_funct_1(sK9) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_57,negated_conjecture,
% 7.91/1.50      ( v1_funct_2(sK9,sK7,sK8) ),
% 7.91/1.50      inference(cnf_transformation,[],[f136]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_62,plain,
% 7.91/1.50      ( v1_funct_2(sK9,sK7,sK8) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2,plain,
% 7.91/1.50      ( v1_xboole_0(k1_xboole_0) ),
% 7.91/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_893,plain,
% 7.91/1.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.91/1.50      theory(equality) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2437,plain,
% 7.91/1.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK8) | sK8 != X0 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_893]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2439,plain,
% 7.91/1.50      ( v1_xboole_0(sK8) | ~ v1_xboole_0(k1_xboole_0) | sK8 != k1_xboole_0 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_2437]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4618,plain,
% 7.91/1.50      ( r1_tarski(k2_relset_1(sK7,sK8,sK9),X0) != iProver_top
% 7.91/1.50      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) = iProver_top ),
% 7.91/1.50      inference(global_propositional_subsumption,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_4073,c_59,c_61,c_62,c_2,c_2439]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4619,plain,
% 7.91/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) = iProver_top
% 7.91/1.50      | r1_tarski(k2_relset_1(sK7,sK8,sK9),X0) != iProver_top ),
% 7.91/1.50      inference(renaming,[status(thm)],[c_4618]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4627,plain,
% 7.91/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_relset_1(sK8,sK6,sK10)))) = iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1924,c_4619]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_43,plain,
% 7.91/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.91/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.50      | ~ r2_hidden(X3,X1)
% 7.91/1.50      | r2_hidden(k1_funct_1(X0,X3),X2)
% 7.91/1.50      | ~ v1_funct_1(X0)
% 7.91/1.50      | k1_xboole_0 = X2 ),
% 7.91/1.50      inference(cnf_transformation,[],[f127]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1929,plain,
% 7.91/1.50      ( k1_xboole_0 = X0
% 7.91/1.50      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.91/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.91/1.50      | r2_hidden(X3,X2) != iProver_top
% 7.91/1.50      | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
% 7.91/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_5026,plain,
% 7.91/1.50      ( k1_relset_1(sK8,sK6,sK10) = k1_xboole_0
% 7.91/1.50      | v1_funct_2(sK9,sK7,k1_relset_1(sK8,sK6,sK10)) != iProver_top
% 7.91/1.50      | r2_hidden(X0,sK7) != iProver_top
% 7.91/1.50      | r2_hidden(k1_funct_1(sK9,X0),k1_relset_1(sK8,sK6,sK10)) = iProver_top
% 7.91/1.50      | v1_funct_1(sK9) != iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_4627,c_1929]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_63,plain,
% 7.91/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_67,plain,
% 7.91/1.50      ( r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_47,plain,
% 7.91/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.91/1.50      | v1_funct_2(X0,X1,X3)
% 7.91/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.50      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 7.91/1.50      | ~ v1_funct_1(X0)
% 7.91/1.50      | k1_xboole_0 = X2 ),
% 7.91/1.50      inference(cnf_transformation,[],[f130]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2571,plain,
% 7.91/1.50      ( v1_funct_2(sK9,sK7,X0)
% 7.91/1.50      | ~ v1_funct_2(sK9,sK7,sK8)
% 7.91/1.50      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 7.91/1.50      | ~ r1_tarski(k2_relset_1(sK7,sK8,sK9),X0)
% 7.91/1.50      | ~ v1_funct_1(sK9)
% 7.91/1.50      | k1_xboole_0 = sK8 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_47]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2818,plain,
% 7.91/1.50      ( v1_funct_2(sK9,sK7,k1_relset_1(sK8,sK6,sK10))
% 7.91/1.50      | ~ v1_funct_2(sK9,sK7,sK8)
% 7.91/1.50      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 7.91/1.50      | ~ r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
% 7.91/1.50      | ~ v1_funct_1(sK9)
% 7.91/1.50      | k1_xboole_0 = sK8 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_2571]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2819,plain,
% 7.91/1.50      ( k1_xboole_0 = sK8
% 7.91/1.50      | v1_funct_2(sK9,sK7,k1_relset_1(sK8,sK6,sK10)) = iProver_top
% 7.91/1.50      | v1_funct_2(sK9,sK7,sK8) != iProver_top
% 7.91/1.50      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 7.91/1.50      | r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) != iProver_top
% 7.91/1.50      | v1_funct_1(sK9) != iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_2818]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_892,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2722,plain,
% 7.91/1.50      ( X0 != X1 | sK8 != X1 | sK8 = X0 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_892]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_3430,plain,
% 7.91/1.50      ( X0 != sK8 | sK8 = X0 | sK8 != sK8 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_2722]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_3432,plain,
% 7.91/1.50      ( sK8 != sK8 | sK8 = k1_xboole_0 | k1_xboole_0 != sK8 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_3430]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_891,plain,( X0 = X0 ),theory(equality) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_3431,plain,
% 7.91/1.50      ( sK8 = sK8 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_891]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6036,plain,
% 7.91/1.50      ( r2_hidden(k1_funct_1(sK9,X0),k1_relset_1(sK8,sK6,sK10)) = iProver_top
% 7.91/1.50      | r2_hidden(X0,sK7) != iProver_top
% 7.91/1.50      | k1_relset_1(sK8,sK6,sK10) = k1_xboole_0 ),
% 7.91/1.50      inference(global_propositional_subsumption,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_5026,c_59,c_61,c_62,c_63,c_67,c_2,c_2439,c_2819,c_3432,
% 7.91/1.50                 c_3431]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6037,plain,
% 7.91/1.50      ( k1_relset_1(sK8,sK6,sK10) = k1_xboole_0
% 7.91/1.50      | r2_hidden(X0,sK7) != iProver_top
% 7.91/1.50      | r2_hidden(k1_funct_1(sK9,X0),k1_relset_1(sK8,sK6,sK10)) = iProver_top ),
% 7.91/1.50      inference(renaming,[status(thm)],[c_6036]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_8066,plain,
% 7.91/1.50      ( k1_relat_1(sK10) = k1_xboole_0
% 7.91/1.50      | r2_hidden(X0,sK7) != iProver_top
% 7.91/1.50      | r2_hidden(k1_funct_1(sK9,X0),k1_relat_1(sK10)) = iProver_top ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_7878,c_6037]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_41,plain,
% 7.91/1.50      ( ~ v5_relat_1(X0,X1)
% 7.91/1.50      | ~ r2_hidden(X2,k1_relat_1(X0))
% 7.91/1.50      | ~ v1_funct_1(X0)
% 7.91/1.50      | ~ v1_relat_1(X0)
% 7.91/1.50      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 7.91/1.50      inference(cnf_transformation,[],[f125]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1931,plain,
% 7.91/1.50      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 7.91/1.50      | v5_relat_1(X1,X0) != iProver_top
% 7.91/1.50      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 7.91/1.50      | v1_funct_1(X1) != iProver_top
% 7.91/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_14696,plain,
% 7.91/1.50      ( k7_partfun1(X0,sK10,k1_funct_1(sK9,X1)) = k1_funct_1(sK10,k1_funct_1(sK9,X1))
% 7.91/1.50      | k1_relat_1(sK10) = k1_xboole_0
% 7.91/1.50      | v5_relat_1(sK10,X0) != iProver_top
% 7.91/1.50      | r2_hidden(X1,sK7) != iProver_top
% 7.91/1.50      | v1_funct_1(sK10) != iProver_top
% 7.91/1.50      | v1_relat_1(sK10) != iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_8066,c_1931]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_55,negated_conjecture,
% 7.91/1.50      ( v1_funct_1(sK10) ),
% 7.91/1.50      inference(cnf_transformation,[],[f138]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_64,plain,
% 7.91/1.50      ( v1_funct_1(sK10) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_65,plain,
% 7.91/1.50      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_34,plain,
% 7.91/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.91/1.50      inference(cnf_transformation,[],[f118]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2417,plain,
% 7.91/1.50      ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
% 7.91/1.50      | v1_relat_1(sK10) ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_34]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2418,plain,
% 7.91/1.50      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) != iProver_top
% 7.91/1.50      | v1_relat_1(sK10) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_2417]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_32317,plain,
% 7.91/1.50      ( k7_partfun1(X0,sK10,k1_funct_1(sK9,X1)) = k1_funct_1(sK10,k1_funct_1(sK9,X1))
% 7.91/1.50      | k1_relat_1(sK10) = k1_xboole_0
% 7.91/1.50      | v5_relat_1(sK10,X0) != iProver_top
% 7.91/1.50      | r2_hidden(X1,sK7) != iProver_top ),
% 7.91/1.50      inference(global_propositional_subsumption,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_14696,c_64,c_65,c_2418]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_32334,plain,
% 7.91/1.50      ( k7_partfun1(X0,sK10,k1_funct_1(sK9,sK11)) = k1_funct_1(sK10,k1_funct_1(sK9,sK11))
% 7.91/1.50      | k1_relat_1(sK10) = k1_xboole_0
% 7.91/1.50      | v5_relat_1(sK10,X0) != iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_9277,c_32317]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_32673,plain,
% 7.91/1.50      ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) = k1_funct_1(sK10,k1_funct_1(sK9,sK11))
% 7.91/1.50      | k1_relat_1(sK10) = k1_xboole_0 ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_6326,c_32334]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_42,plain,
% 7.91/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.91/1.50      | ~ m1_subset_1(X3,X1)
% 7.91/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 7.91/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.50      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 7.91/1.50      | ~ v1_funct_1(X4)
% 7.91/1.50      | ~ v1_funct_1(X0)
% 7.91/1.50      | v1_xboole_0(X2)
% 7.91/1.50      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 7.91/1.50      | k1_xboole_0 = X1 ),
% 7.91/1.50      inference(cnf_transformation,[],[f126]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1930,plain,
% 7.91/1.50      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 7.91/1.50      | k1_xboole_0 = X0
% 7.91/1.50      | v1_funct_2(X3,X0,X1) != iProver_top
% 7.91/1.50      | m1_subset_1(X5,X0) != iProver_top
% 7.91/1.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.91/1.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.91/1.50      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 7.91/1.50      | v1_funct_1(X3) != iProver_top
% 7.91/1.50      | v1_funct_1(X4) != iProver_top
% 7.91/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6168,plain,
% 7.91/1.50      ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),X0) = k1_funct_1(sK10,k1_funct_1(sK9,X0))
% 7.91/1.50      | sK7 = k1_xboole_0
% 7.91/1.50      | v1_funct_2(sK9,sK7,sK8) != iProver_top
% 7.91/1.50      | m1_subset_1(X0,sK7) != iProver_top
% 7.91/1.50      | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) != iProver_top
% 7.91/1.50      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 7.91/1.50      | v1_funct_1(sK10) != iProver_top
% 7.91/1.50      | v1_funct_1(sK9) != iProver_top
% 7.91/1.50      | v1_xboole_0(sK8) = iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1924,c_1930]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_60,plain,
% 7.91/1.50      ( v1_xboole_0(sK8) != iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_13,plain,
% 7.91/1.50      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.91/1.50      | k1_xboole_0 = X0
% 7.91/1.50      | k1_xboole_0 = X1 ),
% 7.91/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_154,plain,
% 7.91/1.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.91/1.50      | k1_xboole_0 = k1_xboole_0 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_13]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_12,plain,
% 7.91/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.91/1.50      inference(cnf_transformation,[],[f147]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_155,plain,
% 7.91/1.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_12]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2489,plain,
% 7.91/1.50      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_892]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2490,plain,
% 7.91/1.50      ( sK7 != k1_xboole_0 | k1_xboole_0 = sK7 | k1_xboole_0 != k1_xboole_0 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_2489]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_7428,plain,
% 7.91/1.50      ( m1_subset_1(X0,sK7) != iProver_top
% 7.91/1.50      | k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),X0) = k1_funct_1(sK10,k1_funct_1(sK9,X0)) ),
% 7.91/1.50      inference(global_propositional_subsumption,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_6168,c_60,c_61,c_62,c_63,c_64,c_65,c_51,c_154,c_155,c_2490]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_7429,plain,
% 7.91/1.50      ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),X0) = k1_funct_1(sK10,k1_funct_1(sK9,X0))
% 7.91/1.50      | m1_subset_1(X0,sK7) != iProver_top ),
% 7.91/1.50      inference(renaming,[status(thm)],[c_7428]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_7436,plain,
% 7.91/1.50      ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) = k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1923,c_7429]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_50,negated_conjecture,
% 7.91/1.50      ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) ),
% 7.91/1.50      inference(cnf_transformation,[],[f143]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_7438,plain,
% 7.91/1.50      ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_7436,c_50]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_32674,plain,
% 7.91/1.50      ( k1_relat_1(sK10) = k1_xboole_0 ),
% 7.91/1.50      inference(global_propositional_subsumption,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_32673,c_7438]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_17,plain,
% 7.91/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.91/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1950,plain,
% 7.91/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.91/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4636,plain,
% 7.91/1.50      ( r1_tarski(sK9,k2_zfmisc_1(sK7,k1_relset_1(sK8,sK6,sK10))) = iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_4627,c_1950]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_8067,plain,
% 7.91/1.50      ( r1_tarski(sK9,k2_zfmisc_1(sK7,k1_relat_1(sK10))) = iProver_top ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_7878,c_4636]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_10,plain,
% 7.91/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 7.91/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1954,plain,
% 7.91/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.91/1.50      | r1_xboole_0(X0,X1) != iProver_top
% 7.91/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_10404,plain,
% 7.91/1.50      ( r1_xboole_0(sK9,k2_zfmisc_1(sK7,k1_relat_1(sK10))) != iProver_top
% 7.91/1.50      | v1_xboole_0(sK9) = iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_8067,c_1954]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_39,plain,
% 7.91/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.91/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.50      | ~ v1_funct_1(X0)
% 7.91/1.50      | ~ v1_xboole_0(X0)
% 7.91/1.50      | v1_xboole_0(X1)
% 7.91/1.50      | v1_xboole_0(X2) ),
% 7.91/1.50      inference(cnf_transformation,[],[f123]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_19,plain,
% 7.91/1.50      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 7.91/1.50      inference(cnf_transformation,[],[f103]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_521,plain,
% 7.91/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.91/1.50      | ~ v1_xboole_0(X0)
% 7.91/1.50      | v1_xboole_0(X1)
% 7.91/1.50      | v1_xboole_0(X2) ),
% 7.91/1.50      inference(global_propositional_subsumption,[status(thm)],[c_39,c_19]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_522,plain,
% 7.91/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.91/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.50      | ~ v1_xboole_0(X0)
% 7.91/1.50      | v1_xboole_0(X1)
% 7.91/1.50      | v1_xboole_0(X2) ),
% 7.91/1.50      inference(renaming,[status(thm)],[c_521]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1916,plain,
% 7.91/1.50      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.91/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.91/1.50      | v1_xboole_0(X0) != iProver_top
% 7.91/1.50      | v1_xboole_0(X2) = iProver_top
% 7.91/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2511,plain,
% 7.91/1.50      ( v1_funct_2(sK9,sK7,sK8) != iProver_top
% 7.91/1.50      | v1_xboole_0(sK9) != iProver_top
% 7.91/1.50      | v1_xboole_0(sK8) = iProver_top
% 7.91/1.50      | v1_xboole_0(sK7) = iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1920,c_1916]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_18556,plain,
% 7.91/1.50      ( r1_xboole_0(sK9,k2_zfmisc_1(sK7,k1_relat_1(sK10))) != iProver_top ),
% 7.91/1.50      inference(global_propositional_subsumption,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_10404,c_60,c_62,c_51,c_2385,c_2511]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_32683,plain,
% 7.91/1.50      ( r1_xboole_0(sK9,k2_zfmisc_1(sK7,k1_xboole_0)) != iProver_top ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_32674,c_18556]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_11,plain,
% 7.91/1.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.91/1.50      inference(cnf_transformation,[],[f146]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_32734,plain,
% 7.91/1.50      ( r1_xboole_0(sK9,k1_xboole_0) != iProver_top ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_32683,c_11]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_5,plain,
% 7.91/1.50      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 7.91/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1958,plain,
% 7.91/1.50      ( r1_xboole_0(X0,X1) = iProver_top
% 7.91/1.50      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_14,plain,
% 7.91/1.50      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 7.91/1.50      inference(cnf_transformation,[],[f98]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1953,plain,
% 7.91/1.50      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_3195,plain,
% 7.91/1.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_11,c_1953]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_5468,plain,
% 7.91/1.50      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1958,c_3195]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_33075,plain,
% 7.91/1.50      ( $false ),
% 7.91/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_32734,c_5468]) ).
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.91/1.50  
% 7.91/1.50  ------                               Statistics
% 7.91/1.50  
% 7.91/1.50  ------ Selected
% 7.91/1.50  
% 7.91/1.50  total_time:                             0.896
% 7.91/1.50  
%------------------------------------------------------------------------------

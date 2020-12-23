%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:42 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 821 expanded)
%              Number of clauses        :  116 ( 239 expanded)
%              Number of leaves         :   24 ( 269 expanded)
%              Depth                    :   21
%              Number of atoms          :  693 (5876 expanded)
%              Number of equality atoms :  286 (1605 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
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

fof(f25,negated_conjecture,(
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
    inference(negated_conjecture,[],[f24])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7) != k7_partfun1(X0,X4,k1_funct_1(X3,sK7))
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK7,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
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
            ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) != k7_partfun1(X0,sK6,k1_funct_1(X3,X5))
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
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
                ( k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK5,X5))
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK5,X1,X2)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
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
                  ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) != k7_partfun1(sK2,X4,k1_funct_1(X3,X5))
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

fof(f72,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7))
    & k1_xboole_0 != sK3
    & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))
    & m1_subset_1(sK7,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f56,f71,f70,f69,f68])).

fof(f120,plain,(
    m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f72])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f122,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f72])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f75,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f117,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f72])).

fof(f23,axiom,(
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

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f114,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f72])).

fof(f115,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f72])).

fof(f116,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f72])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f51])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f119,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f72])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f118,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f72])).

fof(f121,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f72])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f20,axiom,(
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

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

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
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f61])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f125,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f80])).

fof(f123,plain,(
    k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f72])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f124,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f81])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f18,axiom,(
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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f86,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_3258,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3281,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6338,plain,
    ( r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3258,c_3281])).

cnf(c_57,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_42,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3607,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3608,plain,
    ( k1_xboole_0 = sK3
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3607])).

cnf(c_3738,plain,
    ( ~ m1_subset_1(X0,sK3)
    | r2_hidden(X0,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4089,plain,
    ( ~ m1_subset_1(sK7,sK3)
    | r2_hidden(sK7,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3738])).

cnf(c_4090,plain,
    ( m1_subset_1(sK7,sK3) != iProver_top
    | r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4089])).

cnf(c_6458,plain,
    ( r2_hidden(sK7,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6338,c_57,c_42,c_3608,c_4090])).

cnf(c_47,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_3255,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_3262,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_6200,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3255,c_3262])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3270,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5265,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_3255,c_3270])).

cnf(c_6215,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6200,c_5265])).

cnf(c_50,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_49,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_52,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_48,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_53,plain,
    ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_134,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_137,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_140,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2371,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3642,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2371])).

cnf(c_3644,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3642])).

cnf(c_7632,plain,
    ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6215,c_50,c_52,c_53,c_134,c_137,c_140,c_3644])).

cnf(c_7633,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7632])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_3264,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_7645,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(sK5,sK3,X0) != iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X1),X0) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7633,c_3264])).

cnf(c_38,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_3260,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_5205,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,X0) = iProver_top
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3255,c_3260])).

cnf(c_5972,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
    | v1_funct_2(sK5,sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5205,c_50,c_52,c_53,c_134,c_137,c_140,c_3644])).

cnf(c_5973,plain,
    ( v1_funct_2(sK5,sK3,X0) = iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5972])).

cnf(c_5978,plain,
    ( v1_funct_2(sK5,sK3,X0) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5973,c_5265])).

cnf(c_14609,plain,
    ( r2_hidden(k1_funct_1(sK5,X1),X0) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7645,c_52,c_5978])).

cnf(c_14610,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X1),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_14609])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_3257,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_20,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_26,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_575,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_20,c_26])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_579,plain,
    ( ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_575,c_19])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(renaming,[status(thm)],[c_579])).

cnf(c_3248,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_580])).

cnf(c_3853,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3257,c_3248])).

cnf(c_46,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_55,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_4038,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3853,c_55])).

cnf(c_4039,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4038])).

cnf(c_14625,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | k1_relat_1(sK6) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_14610,c_4039])).

cnf(c_43,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_3259,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_5681,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5265,c_3259])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3271,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5518,plain,
    ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_3257,c_3271])).

cnf(c_5826,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5681,c_5518])).

cnf(c_15158,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14625,c_5826])).

cnf(c_15159,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | k1_relat_1(sK6) = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_15158])).

cnf(c_15169,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | k1_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6458,c_15159])).

cnf(c_27,plain,
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

cnf(c_3269,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10404,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
    | sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | m1_subset_1(X2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5265,c_3269])).

cnf(c_51,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_54,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_131,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_132,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2370,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3649,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2370])).

cnf(c_3650,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3649])).

cnf(c_10835,plain,
    ( m1_subset_1(X2,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
    | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10404,c_51,c_52,c_53,c_54,c_42,c_131,c_132,c_3650])).

cnf(c_10836,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | m1_subset_1(X2,sK3) != iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_10835])).

cnf(c_10846,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5518,c_10836])).

cnf(c_56,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_10981,plain,
    ( m1_subset_1(X0,sK3) != iProver_top
    | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10846,c_55,c_56,c_5826])).

cnf(c_10982,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_10981])).

cnf(c_10989,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_3258,c_10982])).

cnf(c_41,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_10991,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_10989,c_41])).

cnf(c_15317,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15169,c_10991])).

cnf(c_15343,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15317,c_5826])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_7640,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_7633])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_4800,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK5,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_4801,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4800])).

cnf(c_560,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_5])).

cnf(c_561,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_4384,plain,
    ( ~ r1_tarski(sK5,k1_xboole_0)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_561])).

cnf(c_4385,plain,
    ( r1_tarski(sK5,k1_xboole_0) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4384])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_13,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_263,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_13])).

cnf(c_264,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(renaming,[status(thm)],[c_263])).

cnf(c_3736,plain,
    ( ~ v1_funct_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_4290,plain,
    ( ~ v1_funct_2(X0,sK3,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3736])).

cnf(c_4361,plain,
    ( ~ v1_funct_2(sK5,sK3,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4290])).

cnf(c_4362,plain,
    ( v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_xboole_0(sK5) != iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4361])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15343,c_7640,c_4801,c_4385,c_4362,c_3608,c_42,c_54,c_53,c_51])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:20:11 EST 2020
% 0.20/0.33  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 3.78/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/0.98  
% 3.78/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.78/0.98  
% 3.78/0.98  ------  iProver source info
% 3.78/0.98  
% 3.78/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.78/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.78/0.98  git: non_committed_changes: false
% 3.78/0.98  git: last_make_outside_of_git: false
% 3.78/0.98  
% 3.78/0.98  ------ 
% 3.78/0.98  
% 3.78/0.98  ------ Input Options
% 3.78/0.98  
% 3.78/0.98  --out_options                           all
% 3.78/0.98  --tptp_safe_out                         true
% 3.78/0.98  --problem_path                          ""
% 3.78/0.98  --include_path                          ""
% 3.78/0.98  --clausifier                            res/vclausify_rel
% 3.78/0.98  --clausifier_options                    --mode clausify
% 3.78/0.98  --stdin                                 false
% 3.78/0.98  --stats_out                             all
% 3.78/0.98  
% 3.78/0.98  ------ General Options
% 3.78/0.98  
% 3.78/0.98  --fof                                   false
% 3.78/0.98  --time_out_real                         305.
% 3.78/0.98  --time_out_virtual                      -1.
% 3.78/0.98  --symbol_type_check                     false
% 3.78/0.98  --clausify_out                          false
% 3.78/0.98  --sig_cnt_out                           false
% 3.78/0.98  --trig_cnt_out                          false
% 3.78/0.98  --trig_cnt_out_tolerance                1.
% 3.78/0.98  --trig_cnt_out_sk_spl                   false
% 3.78/0.98  --abstr_cl_out                          false
% 3.78/0.98  
% 3.78/0.98  ------ Global Options
% 3.78/0.98  
% 3.78/0.98  --schedule                              default
% 3.78/0.98  --add_important_lit                     false
% 3.78/0.98  --prop_solver_per_cl                    1000
% 3.78/0.98  --min_unsat_core                        false
% 3.78/0.98  --soft_assumptions                      false
% 3.78/0.98  --soft_lemma_size                       3
% 3.78/0.98  --prop_impl_unit_size                   0
% 3.78/0.98  --prop_impl_unit                        []
% 3.78/0.98  --share_sel_clauses                     true
% 3.78/0.98  --reset_solvers                         false
% 3.78/0.98  --bc_imp_inh                            [conj_cone]
% 3.78/0.98  --conj_cone_tolerance                   3.
% 3.78/0.98  --extra_neg_conj                        none
% 3.78/0.98  --large_theory_mode                     true
% 3.78/0.98  --prolific_symb_bound                   200
% 3.78/0.98  --lt_threshold                          2000
% 3.78/0.98  --clause_weak_htbl                      true
% 3.78/0.98  --gc_record_bc_elim                     false
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing Options
% 3.78/0.98  
% 3.78/0.98  --preprocessing_flag                    true
% 3.78/0.98  --time_out_prep_mult                    0.1
% 3.78/0.98  --splitting_mode                        input
% 3.78/0.98  --splitting_grd                         true
% 3.78/0.98  --splitting_cvd                         false
% 3.78/0.98  --splitting_cvd_svl                     false
% 3.78/0.98  --splitting_nvd                         32
% 3.78/0.98  --sub_typing                            true
% 3.78/0.98  --prep_gs_sim                           true
% 3.78/0.98  --prep_unflatten                        true
% 3.78/0.98  --prep_res_sim                          true
% 3.78/0.98  --prep_upred                            true
% 3.78/0.98  --prep_sem_filter                       exhaustive
% 3.78/0.98  --prep_sem_filter_out                   false
% 3.78/0.98  --pred_elim                             true
% 3.78/0.98  --res_sim_input                         true
% 3.78/0.98  --eq_ax_congr_red                       true
% 3.78/0.98  --pure_diseq_elim                       true
% 3.78/0.98  --brand_transform                       false
% 3.78/0.98  --non_eq_to_eq                          false
% 3.78/0.98  --prep_def_merge                        true
% 3.78/0.98  --prep_def_merge_prop_impl              false
% 3.78/0.98  --prep_def_merge_mbd                    true
% 3.78/0.98  --prep_def_merge_tr_red                 false
% 3.78/0.98  --prep_def_merge_tr_cl                  false
% 3.78/0.98  --smt_preprocessing                     true
% 3.78/0.98  --smt_ac_axioms                         fast
% 3.78/0.98  --preprocessed_out                      false
% 3.78/0.98  --preprocessed_stats                    false
% 3.78/0.98  
% 3.78/0.98  ------ Abstraction refinement Options
% 3.78/0.98  
% 3.78/0.98  --abstr_ref                             []
% 3.78/0.98  --abstr_ref_prep                        false
% 3.78/0.98  --abstr_ref_until_sat                   false
% 3.78/0.98  --abstr_ref_sig_restrict                funpre
% 3.78/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.78/0.98  --abstr_ref_under                       []
% 3.78/0.98  
% 3.78/0.98  ------ SAT Options
% 3.78/0.98  
% 3.78/0.98  --sat_mode                              false
% 3.78/0.98  --sat_fm_restart_options                ""
% 3.78/0.98  --sat_gr_def                            false
% 3.78/0.98  --sat_epr_types                         true
% 3.78/0.98  --sat_non_cyclic_types                  false
% 3.78/0.98  --sat_finite_models                     false
% 3.78/0.98  --sat_fm_lemmas                         false
% 3.78/0.98  --sat_fm_prep                           false
% 3.78/0.98  --sat_fm_uc_incr                        true
% 3.78/0.98  --sat_out_model                         small
% 3.78/0.98  --sat_out_clauses                       false
% 3.78/0.98  
% 3.78/0.98  ------ QBF Options
% 3.78/0.98  
% 3.78/0.98  --qbf_mode                              false
% 3.78/0.98  --qbf_elim_univ                         false
% 3.78/0.98  --qbf_dom_inst                          none
% 3.78/0.98  --qbf_dom_pre_inst                      false
% 3.78/0.98  --qbf_sk_in                             false
% 3.78/0.98  --qbf_pred_elim                         true
% 3.78/0.98  --qbf_split                             512
% 3.78/0.98  
% 3.78/0.98  ------ BMC1 Options
% 3.78/0.98  
% 3.78/0.98  --bmc1_incremental                      false
% 3.78/0.98  --bmc1_axioms                           reachable_all
% 3.78/0.98  --bmc1_min_bound                        0
% 3.78/0.98  --bmc1_max_bound                        -1
% 3.78/0.98  --bmc1_max_bound_default                -1
% 3.78/0.98  --bmc1_symbol_reachability              true
% 3.78/0.98  --bmc1_property_lemmas                  false
% 3.78/0.98  --bmc1_k_induction                      false
% 3.78/0.98  --bmc1_non_equiv_states                 false
% 3.78/0.98  --bmc1_deadlock                         false
% 3.78/0.98  --bmc1_ucm                              false
% 3.78/0.98  --bmc1_add_unsat_core                   none
% 3.78/0.98  --bmc1_unsat_core_children              false
% 3.78/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.78/0.98  --bmc1_out_stat                         full
% 3.78/0.98  --bmc1_ground_init                      false
% 3.78/0.98  --bmc1_pre_inst_next_state              false
% 3.78/0.98  --bmc1_pre_inst_state                   false
% 3.78/0.98  --bmc1_pre_inst_reach_state             false
% 3.78/0.98  --bmc1_out_unsat_core                   false
% 3.78/0.98  --bmc1_aig_witness_out                  false
% 3.78/0.98  --bmc1_verbose                          false
% 3.78/0.98  --bmc1_dump_clauses_tptp                false
% 3.78/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.78/0.98  --bmc1_dump_file                        -
% 3.78/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.78/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.78/0.98  --bmc1_ucm_extend_mode                  1
% 3.78/0.98  --bmc1_ucm_init_mode                    2
% 3.78/0.98  --bmc1_ucm_cone_mode                    none
% 3.78/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.78/0.98  --bmc1_ucm_relax_model                  4
% 3.78/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.78/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.78/0.98  --bmc1_ucm_layered_model                none
% 3.78/0.98  --bmc1_ucm_max_lemma_size               10
% 3.78/0.98  
% 3.78/0.98  ------ AIG Options
% 3.78/0.98  
% 3.78/0.98  --aig_mode                              false
% 3.78/0.98  
% 3.78/0.98  ------ Instantiation Options
% 3.78/0.98  
% 3.78/0.98  --instantiation_flag                    true
% 3.78/0.98  --inst_sos_flag                         false
% 3.78/0.98  --inst_sos_phase                        true
% 3.78/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.78/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.78/0.98  --inst_lit_sel_side                     num_symb
% 3.78/0.98  --inst_solver_per_active                1400
% 3.78/0.98  --inst_solver_calls_frac                1.
% 3.78/0.98  --inst_passive_queue_type               priority_queues
% 3.78/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.78/0.98  --inst_passive_queues_freq              [25;2]
% 3.78/0.98  --inst_dismatching                      true
% 3.78/0.98  --inst_eager_unprocessed_to_passive     true
% 3.78/0.98  --inst_prop_sim_given                   true
% 3.78/0.98  --inst_prop_sim_new                     false
% 3.78/0.98  --inst_subs_new                         false
% 3.78/0.98  --inst_eq_res_simp                      false
% 3.78/0.98  --inst_subs_given                       false
% 3.78/0.98  --inst_orphan_elimination               true
% 3.78/0.98  --inst_learning_loop_flag               true
% 3.78/0.98  --inst_learning_start                   3000
% 3.78/0.98  --inst_learning_factor                  2
% 3.78/0.98  --inst_start_prop_sim_after_learn       3
% 3.78/0.98  --inst_sel_renew                        solver
% 3.78/0.98  --inst_lit_activity_flag                true
% 3.78/0.98  --inst_restr_to_given                   false
% 3.78/0.98  --inst_activity_threshold               500
% 3.78/0.98  --inst_out_proof                        true
% 3.78/0.98  
% 3.78/0.98  ------ Resolution Options
% 3.78/0.98  
% 3.78/0.98  --resolution_flag                       true
% 3.78/0.98  --res_lit_sel                           adaptive
% 3.78/0.98  --res_lit_sel_side                      none
% 3.78/0.98  --res_ordering                          kbo
% 3.78/0.98  --res_to_prop_solver                    active
% 3.78/0.98  --res_prop_simpl_new                    false
% 3.78/0.98  --res_prop_simpl_given                  true
% 3.78/0.98  --res_passive_queue_type                priority_queues
% 3.78/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.78/0.98  --res_passive_queues_freq               [15;5]
% 3.78/0.98  --res_forward_subs                      full
% 3.78/0.98  --res_backward_subs                     full
% 3.78/0.98  --res_forward_subs_resolution           true
% 3.78/0.98  --res_backward_subs_resolution          true
% 3.78/0.98  --res_orphan_elimination                true
% 3.78/0.98  --res_time_limit                        2.
% 3.78/0.98  --res_out_proof                         true
% 3.78/0.98  
% 3.78/0.98  ------ Superposition Options
% 3.78/0.98  
% 3.78/0.98  --superposition_flag                    true
% 3.78/0.98  --sup_passive_queue_type                priority_queues
% 3.78/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.78/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.78/0.98  --demod_completeness_check              fast
% 3.78/0.98  --demod_use_ground                      true
% 3.78/0.98  --sup_to_prop_solver                    passive
% 3.78/0.98  --sup_prop_simpl_new                    true
% 3.78/0.98  --sup_prop_simpl_given                  true
% 3.78/0.98  --sup_fun_splitting                     false
% 3.78/0.98  --sup_smt_interval                      50000
% 3.78/0.98  
% 3.78/0.98  ------ Superposition Simplification Setup
% 3.78/0.98  
% 3.78/0.98  --sup_indices_passive                   []
% 3.78/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.78/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/0.98  --sup_full_bw                           [BwDemod]
% 3.78/0.98  --sup_immed_triv                        [TrivRules]
% 3.78/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/0.98  --sup_immed_bw_main                     []
% 3.78/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.78/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.78/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.78/0.98  
% 3.78/0.98  ------ Combination Options
% 3.78/0.98  
% 3.78/0.98  --comb_res_mult                         3
% 3.78/0.98  --comb_sup_mult                         2
% 3.78/0.98  --comb_inst_mult                        10
% 3.78/0.98  
% 3.78/0.98  ------ Debug Options
% 3.78/0.98  
% 3.78/0.98  --dbg_backtrace                         false
% 3.78/0.98  --dbg_dump_prop_clauses                 false
% 3.78/0.98  --dbg_dump_prop_clauses_file            -
% 3.78/0.98  --dbg_out_stat                          false
% 3.78/0.98  ------ Parsing...
% 3.78/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/0.98  ------ Proving...
% 3.78/0.98  ------ Problem Properties 
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  clauses                                 43
% 3.78/0.98  conjectures                             10
% 3.78/0.98  EPR                                     14
% 3.78/0.98  Horn                                    33
% 3.78/0.98  unary                                   13
% 3.78/0.98  binary                                  11
% 3.78/0.98  lits                                    123
% 3.78/0.98  lits eq                                 17
% 3.78/0.98  fd_pure                                 0
% 3.78/0.98  fd_pseudo                               0
% 3.78/0.98  fd_cond                                 6
% 3.78/0.98  fd_pseudo_cond                          1
% 3.78/0.98  AC symbols                              0
% 3.78/0.98  
% 3.78/0.98  ------ Schedule dynamic 5 is on 
% 3.78/0.98  
% 3.78/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  ------ 
% 3.78/0.98  Current options:
% 3.78/0.98  ------ 
% 3.78/0.98  
% 3.78/0.98  ------ Input Options
% 3.78/0.98  
% 3.78/0.98  --out_options                           all
% 3.78/0.98  --tptp_safe_out                         true
% 3.78/0.98  --problem_path                          ""
% 3.78/0.98  --include_path                          ""
% 3.78/0.98  --clausifier                            res/vclausify_rel
% 3.78/0.98  --clausifier_options                    --mode clausify
% 3.78/0.98  --stdin                                 false
% 3.78/0.98  --stats_out                             all
% 3.78/0.98  
% 3.78/0.98  ------ General Options
% 3.78/0.98  
% 3.78/0.98  --fof                                   false
% 3.78/0.98  --time_out_real                         305.
% 3.78/0.98  --time_out_virtual                      -1.
% 3.78/0.98  --symbol_type_check                     false
% 3.78/0.98  --clausify_out                          false
% 3.78/0.98  --sig_cnt_out                           false
% 3.78/0.98  --trig_cnt_out                          false
% 3.78/0.98  --trig_cnt_out_tolerance                1.
% 3.78/0.98  --trig_cnt_out_sk_spl                   false
% 3.78/0.98  --abstr_cl_out                          false
% 3.78/0.98  
% 3.78/0.98  ------ Global Options
% 3.78/0.98  
% 3.78/0.98  --schedule                              default
% 3.78/0.98  --add_important_lit                     false
% 3.78/0.98  --prop_solver_per_cl                    1000
% 3.78/0.98  --min_unsat_core                        false
% 3.78/0.98  --soft_assumptions                      false
% 3.78/0.98  --soft_lemma_size                       3
% 3.78/0.98  --prop_impl_unit_size                   0
% 3.78/0.98  --prop_impl_unit                        []
% 3.78/0.98  --share_sel_clauses                     true
% 3.78/0.98  --reset_solvers                         false
% 3.78/0.98  --bc_imp_inh                            [conj_cone]
% 3.78/0.98  --conj_cone_tolerance                   3.
% 3.78/0.98  --extra_neg_conj                        none
% 3.78/0.98  --large_theory_mode                     true
% 3.78/0.98  --prolific_symb_bound                   200
% 3.78/0.98  --lt_threshold                          2000
% 3.78/0.98  --clause_weak_htbl                      true
% 3.78/0.98  --gc_record_bc_elim                     false
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing Options
% 3.78/0.98  
% 3.78/0.98  --preprocessing_flag                    true
% 3.78/0.98  --time_out_prep_mult                    0.1
% 3.78/0.98  --splitting_mode                        input
% 3.78/0.98  --splitting_grd                         true
% 3.78/0.98  --splitting_cvd                         false
% 3.78/0.98  --splitting_cvd_svl                     false
% 3.78/0.98  --splitting_nvd                         32
% 3.78/0.98  --sub_typing                            true
% 3.78/0.98  --prep_gs_sim                           true
% 3.78/0.98  --prep_unflatten                        true
% 3.78/0.98  --prep_res_sim                          true
% 3.78/0.98  --prep_upred                            true
% 3.78/0.98  --prep_sem_filter                       exhaustive
% 3.78/0.98  --prep_sem_filter_out                   false
% 3.78/0.98  --pred_elim                             true
% 3.78/0.98  --res_sim_input                         true
% 3.78/0.98  --eq_ax_congr_red                       true
% 3.78/0.98  --pure_diseq_elim                       true
% 3.78/0.98  --brand_transform                       false
% 3.78/0.98  --non_eq_to_eq                          false
% 3.78/0.98  --prep_def_merge                        true
% 3.78/0.98  --prep_def_merge_prop_impl              false
% 3.78/0.98  --prep_def_merge_mbd                    true
% 3.78/0.98  --prep_def_merge_tr_red                 false
% 3.78/0.98  --prep_def_merge_tr_cl                  false
% 3.78/0.98  --smt_preprocessing                     true
% 3.78/0.98  --smt_ac_axioms                         fast
% 3.78/0.98  --preprocessed_out                      false
% 3.78/0.98  --preprocessed_stats                    false
% 3.78/0.98  
% 3.78/0.98  ------ Abstraction refinement Options
% 3.78/0.98  
% 3.78/0.98  --abstr_ref                             []
% 3.78/0.98  --abstr_ref_prep                        false
% 3.78/0.98  --abstr_ref_until_sat                   false
% 3.78/0.98  --abstr_ref_sig_restrict                funpre
% 3.78/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.78/0.98  --abstr_ref_under                       []
% 3.78/0.98  
% 3.78/0.98  ------ SAT Options
% 3.78/0.98  
% 3.78/0.98  --sat_mode                              false
% 3.78/0.98  --sat_fm_restart_options                ""
% 3.78/0.98  --sat_gr_def                            false
% 3.78/0.98  --sat_epr_types                         true
% 3.78/0.98  --sat_non_cyclic_types                  false
% 3.78/0.98  --sat_finite_models                     false
% 3.78/0.98  --sat_fm_lemmas                         false
% 3.78/0.98  --sat_fm_prep                           false
% 3.78/0.98  --sat_fm_uc_incr                        true
% 3.78/0.98  --sat_out_model                         small
% 3.78/0.98  --sat_out_clauses                       false
% 3.78/0.98  
% 3.78/0.98  ------ QBF Options
% 3.78/0.98  
% 3.78/0.98  --qbf_mode                              false
% 3.78/0.98  --qbf_elim_univ                         false
% 3.78/0.98  --qbf_dom_inst                          none
% 3.78/0.98  --qbf_dom_pre_inst                      false
% 3.78/0.98  --qbf_sk_in                             false
% 3.78/0.98  --qbf_pred_elim                         true
% 3.78/0.98  --qbf_split                             512
% 3.78/0.98  
% 3.78/0.98  ------ BMC1 Options
% 3.78/0.98  
% 3.78/0.98  --bmc1_incremental                      false
% 3.78/0.98  --bmc1_axioms                           reachable_all
% 3.78/0.98  --bmc1_min_bound                        0
% 3.78/0.98  --bmc1_max_bound                        -1
% 3.78/0.98  --bmc1_max_bound_default                -1
% 3.78/0.98  --bmc1_symbol_reachability              true
% 3.78/0.98  --bmc1_property_lemmas                  false
% 3.78/0.98  --bmc1_k_induction                      false
% 3.78/0.98  --bmc1_non_equiv_states                 false
% 3.78/0.98  --bmc1_deadlock                         false
% 3.78/0.98  --bmc1_ucm                              false
% 3.78/0.98  --bmc1_add_unsat_core                   none
% 3.78/0.98  --bmc1_unsat_core_children              false
% 3.78/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.78/0.98  --bmc1_out_stat                         full
% 3.78/0.98  --bmc1_ground_init                      false
% 3.78/0.98  --bmc1_pre_inst_next_state              false
% 3.78/0.98  --bmc1_pre_inst_state                   false
% 3.78/0.98  --bmc1_pre_inst_reach_state             false
% 3.78/0.98  --bmc1_out_unsat_core                   false
% 3.78/0.98  --bmc1_aig_witness_out                  false
% 3.78/0.98  --bmc1_verbose                          false
% 3.78/0.98  --bmc1_dump_clauses_tptp                false
% 3.78/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.78/0.98  --bmc1_dump_file                        -
% 3.78/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.78/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.78/0.98  --bmc1_ucm_extend_mode                  1
% 3.78/0.98  --bmc1_ucm_init_mode                    2
% 3.78/0.98  --bmc1_ucm_cone_mode                    none
% 3.78/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.78/0.98  --bmc1_ucm_relax_model                  4
% 3.78/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.78/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.78/0.98  --bmc1_ucm_layered_model                none
% 3.78/0.98  --bmc1_ucm_max_lemma_size               10
% 3.78/0.98  
% 3.78/0.98  ------ AIG Options
% 3.78/0.98  
% 3.78/0.98  --aig_mode                              false
% 3.78/0.98  
% 3.78/0.98  ------ Instantiation Options
% 3.78/0.98  
% 3.78/0.98  --instantiation_flag                    true
% 3.78/0.98  --inst_sos_flag                         false
% 3.78/0.98  --inst_sos_phase                        true
% 3.78/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.78/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.78/0.98  --inst_lit_sel_side                     none
% 3.78/0.98  --inst_solver_per_active                1400
% 3.78/0.98  --inst_solver_calls_frac                1.
% 3.78/0.98  --inst_passive_queue_type               priority_queues
% 3.78/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.78/0.98  --inst_passive_queues_freq              [25;2]
% 3.78/0.98  --inst_dismatching                      true
% 3.78/0.98  --inst_eager_unprocessed_to_passive     true
% 3.78/0.98  --inst_prop_sim_given                   true
% 3.78/0.98  --inst_prop_sim_new                     false
% 3.78/0.98  --inst_subs_new                         false
% 3.78/0.98  --inst_eq_res_simp                      false
% 3.78/0.98  --inst_subs_given                       false
% 3.78/0.98  --inst_orphan_elimination               true
% 3.78/0.98  --inst_learning_loop_flag               true
% 3.78/0.98  --inst_learning_start                   3000
% 3.78/0.98  --inst_learning_factor                  2
% 3.78/0.98  --inst_start_prop_sim_after_learn       3
% 3.78/0.98  --inst_sel_renew                        solver
% 3.78/0.98  --inst_lit_activity_flag                true
% 3.78/0.98  --inst_restr_to_given                   false
% 3.78/0.98  --inst_activity_threshold               500
% 3.78/0.98  --inst_out_proof                        true
% 3.78/0.98  
% 3.78/0.98  ------ Resolution Options
% 3.78/0.98  
% 3.78/0.98  --resolution_flag                       false
% 3.78/0.98  --res_lit_sel                           adaptive
% 3.78/0.98  --res_lit_sel_side                      none
% 3.78/0.98  --res_ordering                          kbo
% 3.78/0.98  --res_to_prop_solver                    active
% 3.78/0.98  --res_prop_simpl_new                    false
% 3.78/0.98  --res_prop_simpl_given                  true
% 3.78/0.98  --res_passive_queue_type                priority_queues
% 3.78/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.78/0.98  --res_passive_queues_freq               [15;5]
% 3.78/0.98  --res_forward_subs                      full
% 3.78/0.98  --res_backward_subs                     full
% 3.78/0.98  --res_forward_subs_resolution           true
% 3.78/0.98  --res_backward_subs_resolution          true
% 3.78/0.98  --res_orphan_elimination                true
% 3.78/0.98  --res_time_limit                        2.
% 3.78/0.98  --res_out_proof                         true
% 3.78/0.98  
% 3.78/0.98  ------ Superposition Options
% 3.78/0.98  
% 3.78/0.98  --superposition_flag                    true
% 3.78/0.98  --sup_passive_queue_type                priority_queues
% 3.78/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.78/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.78/0.98  --demod_completeness_check              fast
% 3.78/0.98  --demod_use_ground                      true
% 3.78/0.98  --sup_to_prop_solver                    passive
% 3.78/0.98  --sup_prop_simpl_new                    true
% 3.78/0.98  --sup_prop_simpl_given                  true
% 3.78/0.98  --sup_fun_splitting                     false
% 3.78/0.98  --sup_smt_interval                      50000
% 3.78/0.98  
% 3.78/0.98  ------ Superposition Simplification Setup
% 3.78/0.98  
% 3.78/0.98  --sup_indices_passive                   []
% 3.78/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.78/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/0.98  --sup_full_bw                           [BwDemod]
% 3.78/0.98  --sup_immed_triv                        [TrivRules]
% 3.78/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/0.98  --sup_immed_bw_main                     []
% 3.78/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.78/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.78/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.78/0.98  
% 3.78/0.98  ------ Combination Options
% 3.78/0.98  
% 3.78/0.98  --comb_res_mult                         3
% 3.78/0.98  --comb_sup_mult                         2
% 3.78/0.98  --comb_inst_mult                        10
% 3.78/0.98  
% 3.78/0.98  ------ Debug Options
% 3.78/0.98  
% 3.78/0.98  --dbg_backtrace                         false
% 3.78/0.98  --dbg_dump_prop_clauses                 false
% 3.78/0.98  --dbg_dump_prop_clauses_file            -
% 3.78/0.98  --dbg_out_stat                          false
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  ------ Proving...
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  % SZS status Theorem for theBenchmark.p
% 3.78/0.98  
% 3.78/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.78/0.98  
% 3.78/0.98  fof(f24,conjecture,(
% 3.78/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f25,negated_conjecture,(
% 3.78/0.98    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 3.78/0.98    inference(negated_conjecture,[],[f24])).
% 3.78/0.98  
% 3.78/0.98  fof(f55,plain,(
% 3.78/0.98    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 3.78/0.98    inference(ennf_transformation,[],[f25])).
% 3.78/0.98  
% 3.78/0.98  fof(f56,plain,(
% 3.78/0.98    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 3.78/0.98    inference(flattening,[],[f55])).
% 3.78/0.98  
% 3.78/0.98  fof(f71,plain,(
% 3.78/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7) != k7_partfun1(X0,X4,k1_funct_1(X3,sK7)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK7,X1))) )),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f70,plain,(
% 3.78/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) != k7_partfun1(X0,sK6,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6)) & m1_subset_1(X5,X1)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK6))) )),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f69,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK5,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f68,plain,(
% 3.78/0.98    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) != k7_partfun1(sK2,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f72,plain,(
% 3.78/0.98    (((k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 3.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f56,f71,f70,f69,f68])).
% 3.78/0.98  
% 3.78/0.98  fof(f120,plain,(
% 3.78/0.98    m1_subset_1(sK7,sK3)),
% 3.78/0.98    inference(cnf_transformation,[],[f72])).
% 3.78/0.98  
% 3.78/0.98  fof(f8,axiom,(
% 3.78/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f31,plain,(
% 3.78/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.78/0.98    inference(ennf_transformation,[],[f8])).
% 3.78/0.98  
% 3.78/0.98  fof(f32,plain,(
% 3.78/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.78/0.98    inference(flattening,[],[f31])).
% 3.78/0.98  
% 3.78/0.98  fof(f83,plain,(
% 3.78/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f32])).
% 3.78/0.98  
% 3.78/0.98  fof(f122,plain,(
% 3.78/0.98    k1_xboole_0 != sK3),
% 3.78/0.98    inference(cnf_transformation,[],[f72])).
% 3.78/0.98  
% 3.78/0.98  fof(f2,axiom,(
% 3.78/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f27,plain,(
% 3.78/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.78/0.98    inference(ennf_transformation,[],[f2])).
% 3.78/0.98  
% 3.78/0.98  fof(f75,plain,(
% 3.78/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f27])).
% 3.78/0.98  
% 3.78/0.98  fof(f117,plain,(
% 3.78/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.78/0.98    inference(cnf_transformation,[],[f72])).
% 3.78/0.98  
% 3.78/0.98  fof(f23,axiom,(
% 3.78/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f53,plain,(
% 3.78/0.98    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.78/0.98    inference(ennf_transformation,[],[f23])).
% 3.78/0.98  
% 3.78/0.98  fof(f54,plain,(
% 3.78/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.78/0.98    inference(flattening,[],[f53])).
% 3.78/0.98  
% 3.78/0.98  fof(f112,plain,(
% 3.78/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f54])).
% 3.78/0.98  
% 3.78/0.98  fof(f17,axiom,(
% 3.78/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f42,plain,(
% 3.78/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.98    inference(ennf_transformation,[],[f17])).
% 3.78/0.98  
% 3.78/0.98  fof(f95,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/0.98    inference(cnf_transformation,[],[f42])).
% 3.78/0.98  
% 3.78/0.98  fof(f114,plain,(
% 3.78/0.98    ~v1_xboole_0(sK4)),
% 3.78/0.98    inference(cnf_transformation,[],[f72])).
% 3.78/0.98  
% 3.78/0.98  fof(f115,plain,(
% 3.78/0.98    v1_funct_1(sK5)),
% 3.78/0.98    inference(cnf_transformation,[],[f72])).
% 3.78/0.98  
% 3.78/0.98  fof(f116,plain,(
% 3.78/0.98    v1_funct_2(sK5,sK3,sK4)),
% 3.78/0.98    inference(cnf_transformation,[],[f72])).
% 3.78/0.98  
% 3.78/0.98  fof(f5,axiom,(
% 3.78/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f28,plain,(
% 3.78/0.98    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 3.78/0.98    inference(ennf_transformation,[],[f5])).
% 3.78/0.98  
% 3.78/0.98  fof(f29,plain,(
% 3.78/0.98    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 3.78/0.98    inference(flattening,[],[f28])).
% 3.78/0.98  
% 3.78/0.98  fof(f78,plain,(
% 3.78/0.98    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f29])).
% 3.78/0.98  
% 3.78/0.98  fof(f4,axiom,(
% 3.78/0.98    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f77,plain,(
% 3.78/0.98    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f4])).
% 3.78/0.98  
% 3.78/0.98  fof(f3,axiom,(
% 3.78/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f76,plain,(
% 3.78/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f3])).
% 3.78/0.98  
% 3.78/0.98  fof(f22,axiom,(
% 3.78/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f51,plain,(
% 3.78/0.98    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.78/0.98    inference(ennf_transformation,[],[f22])).
% 3.78/0.98  
% 3.78/0.98  fof(f52,plain,(
% 3.78/0.98    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.78/0.98    inference(flattening,[],[f51])).
% 3.78/0.98  
% 3.78/0.98  fof(f107,plain,(
% 3.78/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f52])).
% 3.78/0.98  
% 3.78/0.98  fof(f110,plain,(
% 3.78/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f54])).
% 3.78/0.98  
% 3.78/0.98  fof(f119,plain,(
% 3.78/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 3.78/0.98    inference(cnf_transformation,[],[f72])).
% 3.78/0.98  
% 3.78/0.98  fof(f15,axiom,(
% 3.78/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f26,plain,(
% 3.78/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.78/0.98    inference(pure_predicate_removal,[],[f15])).
% 3.78/0.98  
% 3.78/0.98  fof(f40,plain,(
% 3.78/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.98    inference(ennf_transformation,[],[f26])).
% 3.78/0.98  
% 3.78/0.98  fof(f93,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/0.98    inference(cnf_transformation,[],[f40])).
% 3.78/0.98  
% 3.78/0.98  fof(f19,axiom,(
% 3.78/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f45,plain,(
% 3.78/0.98    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.78/0.98    inference(ennf_transformation,[],[f19])).
% 3.78/0.98  
% 3.78/0.98  fof(f46,plain,(
% 3.78/0.98    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.78/0.98    inference(flattening,[],[f45])).
% 3.78/0.98  
% 3.78/0.98  fof(f99,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f46])).
% 3.78/0.98  
% 3.78/0.98  fof(f14,axiom,(
% 3.78/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f39,plain,(
% 3.78/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.98    inference(ennf_transformation,[],[f14])).
% 3.78/0.98  
% 3.78/0.98  fof(f92,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/0.98    inference(cnf_transformation,[],[f39])).
% 3.78/0.98  
% 3.78/0.98  fof(f118,plain,(
% 3.78/0.98    v1_funct_1(sK6)),
% 3.78/0.98    inference(cnf_transformation,[],[f72])).
% 3.78/0.98  
% 3.78/0.98  fof(f121,plain,(
% 3.78/0.98    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))),
% 3.78/0.98    inference(cnf_transformation,[],[f72])).
% 3.78/0.98  
% 3.78/0.98  fof(f16,axiom,(
% 3.78/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f41,plain,(
% 3.78/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.98    inference(ennf_transformation,[],[f16])).
% 3.78/0.98  
% 3.78/0.98  fof(f94,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/0.98    inference(cnf_transformation,[],[f41])).
% 3.78/0.98  
% 3.78/0.98  fof(f20,axiom,(
% 3.78/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f47,plain,(
% 3.78/0.98    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 3.78/0.98    inference(ennf_transformation,[],[f20])).
% 3.78/0.98  
% 3.78/0.98  fof(f48,plain,(
% 3.78/0.98    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 3.78/0.98    inference(flattening,[],[f47])).
% 3.78/0.98  
% 3.78/0.98  fof(f100,plain,(
% 3.78/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f48])).
% 3.78/0.98  
% 3.78/0.98  fof(f6,axiom,(
% 3.78/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f61,plain,(
% 3.78/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.78/0.98    inference(nnf_transformation,[],[f6])).
% 3.78/0.98  
% 3.78/0.98  fof(f62,plain,(
% 3.78/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.78/0.98    inference(flattening,[],[f61])).
% 3.78/0.98  
% 3.78/0.98  fof(f79,plain,(
% 3.78/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f62])).
% 3.78/0.98  
% 3.78/0.98  fof(f80,plain,(
% 3.78/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.78/0.98    inference(cnf_transformation,[],[f62])).
% 3.78/0.98  
% 3.78/0.98  fof(f125,plain,(
% 3.78/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.78/0.98    inference(equality_resolution,[],[f80])).
% 3.78/0.98  
% 3.78/0.98  fof(f123,plain,(
% 3.78/0.98    k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7))),
% 3.78/0.98    inference(cnf_transformation,[],[f72])).
% 3.78/0.98  
% 3.78/0.98  fof(f81,plain,(
% 3.78/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.78/0.98    inference(cnf_transformation,[],[f62])).
% 3.78/0.98  
% 3.78/0.98  fof(f124,plain,(
% 3.78/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.78/0.98    inference(equality_resolution,[],[f81])).
% 3.78/0.98  
% 3.78/0.98  fof(f9,axiom,(
% 3.78/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f63,plain,(
% 3.78/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.78/0.98    inference(nnf_transformation,[],[f9])).
% 3.78/0.98  
% 3.78/0.98  fof(f84,plain,(
% 3.78/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.78/0.98    inference(cnf_transformation,[],[f63])).
% 3.78/0.98  
% 3.78/0.98  fof(f18,axiom,(
% 3.78/0.98    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f43,plain,(
% 3.78/0.98    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.78/0.98    inference(ennf_transformation,[],[f18])).
% 3.78/0.98  
% 3.78/0.98  fof(f44,plain,(
% 3.78/0.98    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.78/0.98    inference(flattening,[],[f43])).
% 3.78/0.98  
% 3.78/0.98  fof(f97,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f44])).
% 3.78/0.98  
% 3.78/0.98  fof(f10,axiom,(
% 3.78/0.98    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f33,plain,(
% 3.78/0.98    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 3.78/0.98    inference(ennf_transformation,[],[f10])).
% 3.78/0.98  
% 3.78/0.98  fof(f86,plain,(
% 3.78/0.98    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f33])).
% 3.78/0.98  
% 3.78/0.98  cnf(c_44,negated_conjecture,
% 3.78/0.98      ( m1_subset_1(sK7,sK3) ),
% 3.78/0.98      inference(cnf_transformation,[],[f120]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3258,plain,
% 3.78/0.98      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_10,plain,
% 3.78/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.78/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3281,plain,
% 3.78/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.78/0.98      | r2_hidden(X0,X1) = iProver_top
% 3.78/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_6338,plain,
% 3.78/0.98      ( r2_hidden(sK7,sK3) = iProver_top
% 3.78/0.98      | v1_xboole_0(sK3) = iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_3258,c_3281]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_57,plain,
% 3.78/0.98      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_42,negated_conjecture,
% 3.78/0.98      ( k1_xboole_0 != sK3 ),
% 3.78/0.98      inference(cnf_transformation,[],[f122]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2,plain,
% 3.78/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.78/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3607,plain,
% 3.78/0.98      ( ~ v1_xboole_0(sK3) | k1_xboole_0 = sK3 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3608,plain,
% 3.78/0.98      ( k1_xboole_0 = sK3 | v1_xboole_0(sK3) != iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_3607]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3738,plain,
% 3.78/0.98      ( ~ m1_subset_1(X0,sK3) | r2_hidden(X0,sK3) | v1_xboole_0(sK3) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4089,plain,
% 3.78/0.98      ( ~ m1_subset_1(sK7,sK3) | r2_hidden(sK7,sK3) | v1_xboole_0(sK3) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_3738]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4090,plain,
% 3.78/0.98      ( m1_subset_1(sK7,sK3) != iProver_top
% 3.78/0.98      | r2_hidden(sK7,sK3) = iProver_top
% 3.78/0.98      | v1_xboole_0(sK3) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_4089]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_6458,plain,
% 3.78/0.98      ( r2_hidden(sK7,sK3) = iProver_top ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_6338,c_57,c_42,c_3608,c_4090]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_47,negated_conjecture,
% 3.78/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.78/0.98      inference(cnf_transformation,[],[f117]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3255,plain,
% 3.78/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_36,plain,
% 3.78/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.78/0.98      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 3.78/0.98      | ~ v1_funct_1(X0)
% 3.78/0.98      | k1_xboole_0 = X2 ),
% 3.78/0.98      inference(cnf_transformation,[],[f112]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3262,plain,
% 3.78/0.98      ( k1_xboole_0 = X0
% 3.78/0.98      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.78/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.78/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 3.78/0.98      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 3.78/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_6200,plain,
% 3.78/0.98      ( sK4 = k1_xboole_0
% 3.78/0.98      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.78/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.78/0.98      | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
% 3.78/0.98      | v1_funct_1(sK5) != iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_3255,c_3262]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_22,plain,
% 3.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.78/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3270,plain,
% 3.78/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.78/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5265,plain,
% 3.78/0.98      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_3255,c_3270]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_6215,plain,
% 3.78/0.98      ( sK4 = k1_xboole_0
% 3.78/0.98      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.78/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.78/0.98      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.78/0.98      | v1_funct_1(sK5) != iProver_top ),
% 3.78/0.98      inference(light_normalisation,[status(thm)],[c_6200,c_5265]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_50,negated_conjecture,
% 3.78/0.98      ( ~ v1_xboole_0(sK4) ),
% 3.78/0.98      inference(cnf_transformation,[],[f114]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_49,negated_conjecture,
% 3.78/0.98      ( v1_funct_1(sK5) ),
% 3.78/0.98      inference(cnf_transformation,[],[f115]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_52,plain,
% 3.78/0.98      ( v1_funct_1(sK5) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_48,negated_conjecture,
% 3.78/0.98      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.78/0.98      inference(cnf_transformation,[],[f116]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_53,plain,
% 3.78/0.98      ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5,plain,
% 3.78/0.98      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 3.78/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_134,plain,
% 3.78/0.98      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 3.78/0.98      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.78/0.98      | v1_xboole_0(k1_xboole_0) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4,plain,
% 3.78/0.98      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.78/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_137,plain,
% 3.78/0.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3,plain,
% 3.78/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.78/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_140,plain,
% 3.78/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2371,plain,
% 3.78/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.78/0.98      theory(equality) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3642,plain,
% 3.78/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_2371]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3644,plain,
% 3.78/0.98      ( v1_xboole_0(sK4)
% 3.78/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 3.78/0.98      | sK4 != k1_xboole_0 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_3642]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_7632,plain,
% 3.78/0.98      ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.78/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_6215,c_50,c_52,c_53,c_134,c_137,c_140,c_3644]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_7633,plain,
% 3.78/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.78/0.98      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_7632]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_34,plain,
% 3.78/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.98      | ~ r2_hidden(X3,X1)
% 3.78/0.98      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.78/0.98      | ~ v1_funct_1(X0)
% 3.78/0.98      | k1_xboole_0 = X2 ),
% 3.78/0.98      inference(cnf_transformation,[],[f107]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3264,plain,
% 3.78/0.98      ( k1_xboole_0 = X0
% 3.78/0.98      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.78/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.78/0.98      | r2_hidden(X3,X2) != iProver_top
% 3.78/0.98      | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
% 3.78/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_7645,plain,
% 3.78/0.98      ( k1_xboole_0 = X0
% 3.78/0.98      | v1_funct_2(sK5,sK3,X0) != iProver_top
% 3.78/0.98      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.78/0.98      | r2_hidden(X1,sK3) != iProver_top
% 3.78/0.98      | r2_hidden(k1_funct_1(sK5,X1),X0) = iProver_top
% 3.78/0.98      | v1_funct_1(sK5) != iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_7633,c_3264]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_38,plain,
% 3.78/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.78/0.98      | v1_funct_2(X0,X1,X3)
% 3.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.98      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 3.78/0.98      | ~ v1_funct_1(X0)
% 3.78/0.98      | k1_xboole_0 = X2 ),
% 3.78/0.98      inference(cnf_transformation,[],[f110]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3260,plain,
% 3.78/0.98      ( k1_xboole_0 = X0
% 3.78/0.98      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.78/0.98      | v1_funct_2(X1,X2,X3) = iProver_top
% 3.78/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.78/0.98      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 3.78/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5205,plain,
% 3.78/0.98      ( sK4 = k1_xboole_0
% 3.78/0.98      | v1_funct_2(sK5,sK3,X0) = iProver_top
% 3.78/0.98      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.78/0.98      | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
% 3.78/0.98      | v1_funct_1(sK5) != iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_3255,c_3260]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5972,plain,
% 3.78/0.98      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
% 3.78/0.98      | v1_funct_2(sK5,sK3,X0) = iProver_top ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_5205,c_50,c_52,c_53,c_134,c_137,c_140,c_3644]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5973,plain,
% 3.78/0.98      ( v1_funct_2(sK5,sK3,X0) = iProver_top
% 3.78/0.98      | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_5972]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5978,plain,
% 3.78/0.98      ( v1_funct_2(sK5,sK3,X0) = iProver_top
% 3.78/0.98      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 3.78/0.98      inference(light_normalisation,[status(thm)],[c_5973,c_5265]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_14609,plain,
% 3.78/0.98      ( r2_hidden(k1_funct_1(sK5,X1),X0) = iProver_top
% 3.78/0.98      | r2_hidden(X1,sK3) != iProver_top
% 3.78/0.98      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.78/0.98      | k1_xboole_0 = X0 ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_7645,c_52,c_5978]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_14610,plain,
% 3.78/0.98      ( k1_xboole_0 = X0
% 3.78/0.98      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.78/0.98      | r2_hidden(X1,sK3) != iProver_top
% 3.78/0.98      | r2_hidden(k1_funct_1(sK5,X1),X0) = iProver_top ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_14609]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_45,negated_conjecture,
% 3.78/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 3.78/0.98      inference(cnf_transformation,[],[f119]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3257,plain,
% 3.78/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_20,plain,
% 3.78/0.98      ( v5_relat_1(X0,X1)
% 3.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.78/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_26,plain,
% 3.78/0.98      ( ~ v5_relat_1(X0,X1)
% 3.78/0.98      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.78/0.98      | ~ v1_relat_1(X0)
% 3.78/0.98      | ~ v1_funct_1(X0)
% 3.78/0.98      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.78/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_575,plain,
% 3.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.98      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.78/0.98      | ~ v1_relat_1(X0)
% 3.78/0.98      | ~ v1_funct_1(X0)
% 3.78/0.98      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.78/0.98      inference(resolution,[status(thm)],[c_20,c_26]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_19,plain,
% 3.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.98      | v1_relat_1(X0) ),
% 3.78/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_579,plain,
% 3.78/0.98      ( ~ r2_hidden(X3,k1_relat_1(X0))
% 3.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.98      | ~ v1_funct_1(X0)
% 3.78/0.98      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_575,c_19]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_580,plain,
% 3.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.98      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.78/0.98      | ~ v1_funct_1(X0)
% 3.78/0.98      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_579]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3248,plain,
% 3.78/0.98      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 3.78/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 3.78/0.98      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 3.78/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_580]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3853,plain,
% 3.78/0.98      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 3.78/0.98      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.78/0.98      | v1_funct_1(sK6) != iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_3257,c_3248]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_46,negated_conjecture,
% 3.78/0.98      ( v1_funct_1(sK6) ),
% 3.78/0.98      inference(cnf_transformation,[],[f118]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_55,plain,
% 3.78/0.98      ( v1_funct_1(sK6) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4038,plain,
% 3.78/0.98      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.78/0.98      | k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0) ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_3853,c_55]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4039,plain,
% 3.78/0.98      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 3.78/0.98      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_4038]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_14625,plain,
% 3.78/0.98      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.78/0.98      | k1_relat_1(sK6) = k1_xboole_0
% 3.78/0.98      | r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) != iProver_top
% 3.78/0.98      | r2_hidden(X0,sK3) != iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_14610,c_4039]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_43,negated_conjecture,
% 3.78/0.98      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
% 3.78/0.98      inference(cnf_transformation,[],[f121]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3259,plain,
% 3.78/0.98      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5681,plain,
% 3.78/0.98      ( r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 3.78/0.98      inference(demodulation,[status(thm)],[c_5265,c_3259]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_21,plain,
% 3.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.78/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3271,plain,
% 3.78/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.78/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5518,plain,
% 3.78/0.98      ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_3257,c_3271]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5826,plain,
% 3.78/0.98      ( r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) = iProver_top ),
% 3.78/0.98      inference(light_normalisation,[status(thm)],[c_5681,c_5518]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_15158,plain,
% 3.78/0.98      ( k1_relat_1(sK6) = k1_xboole_0
% 3.78/0.98      | k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.78/0.98      | r2_hidden(X0,sK3) != iProver_top ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_14625,c_5826]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_15159,plain,
% 3.78/0.98      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.78/0.98      | k1_relat_1(sK6) = k1_xboole_0
% 3.78/0.98      | r2_hidden(X0,sK3) != iProver_top ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_15158]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_15169,plain,
% 3.78/0.98      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
% 3.78/0.98      | k1_relat_1(sK6) = k1_xboole_0 ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_6458,c_15159]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_27,plain,
% 3.78/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.78/0.98      | ~ m1_subset_1(X3,X1)
% 3.78/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 3.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.98      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 3.78/0.98      | ~ v1_funct_1(X4)
% 3.78/0.98      | ~ v1_funct_1(X0)
% 3.78/0.98      | v1_xboole_0(X2)
% 3.78/0.98      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 3.78/0.98      | k1_xboole_0 = X1 ),
% 3.78/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3269,plain,
% 3.78/0.98      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 3.78/0.98      | k1_xboole_0 = X0
% 3.78/0.98      | v1_funct_2(X3,X0,X1) != iProver_top
% 3.78/0.98      | m1_subset_1(X5,X0) != iProver_top
% 3.78/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.78/0.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.78/0.98      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 3.78/0.98      | v1_funct_1(X3) != iProver_top
% 3.78/0.98      | v1_funct_1(X4) != iProver_top
% 3.78/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_10404,plain,
% 3.78/0.98      ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
% 3.78/0.98      | sK3 = k1_xboole_0
% 3.78/0.98      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.78/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
% 3.78/0.98      | m1_subset_1(X2,sK3) != iProver_top
% 3.78/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.78/0.98      | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
% 3.78/0.98      | v1_funct_1(X1) != iProver_top
% 3.78/0.98      | v1_funct_1(sK5) != iProver_top
% 3.78/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_5265,c_3269]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_51,plain,
% 3.78/0.98      ( v1_xboole_0(sK4) != iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_54,plain,
% 3.78/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_8,plain,
% 3.78/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.78/0.98      | k1_xboole_0 = X0
% 3.78/0.98      | k1_xboole_0 = X1 ),
% 3.78/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_131,plain,
% 3.78/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.78/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_7,plain,
% 3.78/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.78/0.98      inference(cnf_transformation,[],[f125]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_132,plain,
% 3.78/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2370,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3649,plain,
% 3.78/0.98      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_2370]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3650,plain,
% 3.78/0.98      ( sK3 != k1_xboole_0
% 3.78/0.98      | k1_xboole_0 = sK3
% 3.78/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_3649]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_10835,plain,
% 3.78/0.98      ( m1_subset_1(X2,sK3) != iProver_top
% 3.78/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
% 3.78/0.98      | k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
% 3.78/0.98      | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
% 3.78/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_10404,c_51,c_52,c_53,c_54,c_42,c_131,c_132,c_3650]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_10836,plain,
% 3.78/0.98      ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
% 3.78/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
% 3.78/0.98      | m1_subset_1(X2,sK3) != iProver_top
% 3.78/0.98      | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
% 3.78/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_10835]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_10846,plain,
% 3.78/0.98      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.78/0.98      | m1_subset_1(X0,sK3) != iProver_top
% 3.78/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 3.78/0.98      | r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) != iProver_top
% 3.78/0.98      | v1_funct_1(sK6) != iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_5518,c_10836]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_56,plain,
% 3.78/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_10981,plain,
% 3.78/0.98      ( m1_subset_1(X0,sK3) != iProver_top
% 3.78/0.98      | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_10846,c_55,c_56,c_5826]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_10982,plain,
% 3.78/0.98      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.78/0.98      | m1_subset_1(X0,sK3) != iProver_top ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_10981]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_10989,plain,
% 3.78/0.98      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_3258,c_10982]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_41,negated_conjecture,
% 3.78/0.98      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
% 3.78/0.98      inference(cnf_transformation,[],[f123]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_10991,plain,
% 3.78/0.98      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 3.78/0.98      inference(demodulation,[status(thm)],[c_10989,c_41]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_15317,plain,
% 3.78/0.98      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_15169,c_10991]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_15343,plain,
% 3.78/0.98      ( r1_tarski(k2_relat_1(sK5),k1_xboole_0) = iProver_top ),
% 3.78/0.98      inference(demodulation,[status(thm)],[c_15317,c_5826]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_6,plain,
% 3.78/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.78/0.98      inference(cnf_transformation,[],[f124]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_7640,plain,
% 3.78/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.78/0.98      | r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_6,c_7633]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_12,plain,
% 3.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.78/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4800,plain,
% 3.78/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
% 3.78/0.98      | r1_tarski(sK5,k1_xboole_0) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4801,plain,
% 3.78/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.78/0.98      | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_4800]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_560,plain,
% 3.78/0.98      ( ~ r1_tarski(X0,X1)
% 3.78/0.98      | v1_xboole_0(X0)
% 3.78/0.98      | X0 != X2
% 3.78/0.98      | k1_xboole_0 != X1 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_5]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_561,plain,
% 3.78/0.98      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_560]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4384,plain,
% 3.78/0.98      ( ~ r1_tarski(sK5,k1_xboole_0) | v1_xboole_0(sK5) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_561]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4385,plain,
% 3.78/0.98      ( r1_tarski(sK5,k1_xboole_0) != iProver_top
% 3.78/0.98      | v1_xboole_0(sK5) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_4384]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_24,plain,
% 3.78/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.98      | ~ v1_funct_1(X0)
% 3.78/0.98      | ~ v1_xboole_0(X0)
% 3.78/0.98      | v1_xboole_0(X1)
% 3.78/0.98      | v1_xboole_0(X2) ),
% 3.78/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_13,plain,
% 3.78/0.98      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 3.78/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_263,plain,
% 3.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.98      | ~ v1_funct_2(X0,X1,X2)
% 3.78/0.98      | ~ v1_xboole_0(X0)
% 3.78/0.98      | v1_xboole_0(X1)
% 3.78/0.98      | v1_xboole_0(X2) ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_24,c_13]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_264,plain,
% 3.78/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.98      | ~ v1_xboole_0(X0)
% 3.78/0.98      | v1_xboole_0(X1)
% 3.78/0.98      | v1_xboole_0(X2) ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_263]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3736,plain,
% 3.78/0.98      ( ~ v1_funct_2(X0,sK3,X1)
% 3.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
% 3.78/0.98      | ~ v1_xboole_0(X0)
% 3.78/0.98      | v1_xboole_0(X1)
% 3.78/0.98      | v1_xboole_0(sK3) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_264]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4290,plain,
% 3.78/0.98      ( ~ v1_funct_2(X0,sK3,sK4)
% 3.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.78/0.98      | ~ v1_xboole_0(X0)
% 3.78/0.98      | v1_xboole_0(sK4)
% 3.78/0.98      | v1_xboole_0(sK3) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_3736]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4361,plain,
% 3.78/0.98      ( ~ v1_funct_2(sK5,sK3,sK4)
% 3.78/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.78/0.98      | ~ v1_xboole_0(sK5)
% 3.78/0.98      | v1_xboole_0(sK4)
% 3.78/0.98      | v1_xboole_0(sK3) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_4290]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4362,plain,
% 3.78/0.98      ( v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.78/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.78/0.98      | v1_xboole_0(sK5) != iProver_top
% 3.78/0.98      | v1_xboole_0(sK4) = iProver_top
% 3.78/0.98      | v1_xboole_0(sK3) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_4361]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(contradiction,plain,
% 3.78/0.98      ( $false ),
% 3.78/0.98      inference(minisat,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_15343,c_7640,c_4801,c_4385,c_4362,c_3608,c_42,c_54,
% 3.78/0.98                 c_53,c_51]) ).
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.78/0.98  
% 3.78/0.98  ------                               Statistics
% 3.78/0.98  
% 3.78/0.98  ------ General
% 3.78/0.98  
% 3.78/0.98  abstr_ref_over_cycles:                  0
% 3.78/0.98  abstr_ref_under_cycles:                 0
% 3.78/0.98  gc_basic_clause_elim:                   0
% 3.78/0.98  forced_gc_time:                         0
% 3.78/0.98  parsing_time:                           0.011
% 3.78/0.98  unif_index_cands_time:                  0.
% 3.78/0.98  unif_index_add_time:                    0.
% 3.78/0.98  orderings_time:                         0.
% 3.78/0.98  out_proof_time:                         0.015
% 3.78/0.98  total_time:                             0.446
% 3.78/0.98  num_of_symbols:                         59
% 3.78/0.98  num_of_terms:                           17819
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing
% 3.78/0.98  
% 3.78/0.98  num_of_splits:                          0
% 3.78/0.98  num_of_split_atoms:                     0
% 3.78/0.98  num_of_reused_defs:                     0
% 3.78/0.98  num_eq_ax_congr_red:                    24
% 3.78/0.98  num_of_sem_filtered_clauses:            1
% 3.78/0.98  num_of_subtypes:                        0
% 3.78/0.98  monotx_restored_types:                  0
% 3.78/0.98  sat_num_of_epr_types:                   0
% 3.78/0.98  sat_num_of_non_cyclic_types:            0
% 3.78/0.98  sat_guarded_non_collapsed_types:        0
% 3.78/0.98  num_pure_diseq_elim:                    0
% 3.78/0.98  simp_replaced_by:                       0
% 3.78/0.98  res_preprocessed:                       209
% 3.78/0.98  prep_upred:                             0
% 3.78/0.98  prep_unflattend:                        82
% 3.78/0.98  smt_new_axioms:                         0
% 3.78/0.98  pred_elim_cands:                        7
% 3.78/0.98  pred_elim:                              2
% 3.78/0.98  pred_elim_cl:                           2
% 3.78/0.98  pred_elim_cycles:                       6
% 3.78/0.98  merged_defs:                            8
% 3.78/0.98  merged_defs_ncl:                        0
% 3.78/0.98  bin_hyper_res:                          9
% 3.78/0.98  prep_cycles:                            4
% 3.78/0.98  pred_elim_time:                         0.028
% 3.78/0.98  splitting_time:                         0.
% 3.78/0.98  sem_filter_time:                        0.
% 3.78/0.98  monotx_time:                            0.001
% 3.78/0.98  subtype_inf_time:                       0.
% 3.78/0.98  
% 3.78/0.98  ------ Problem properties
% 3.78/0.98  
% 3.78/0.98  clauses:                                43
% 3.78/0.98  conjectures:                            10
% 3.78/0.98  epr:                                    14
% 3.78/0.98  horn:                                   33
% 3.78/0.98  ground:                                 10
% 3.78/0.98  unary:                                  13
% 3.78/0.98  binary:                                 11
% 3.78/0.98  lits:                                   123
% 3.78/0.98  lits_eq:                                17
% 3.78/0.98  fd_pure:                                0
% 3.78/0.98  fd_pseudo:                              0
% 3.78/0.98  fd_cond:                                6
% 3.78/0.98  fd_pseudo_cond:                         1
% 3.78/0.98  ac_symbols:                             0
% 3.78/0.98  
% 3.78/0.98  ------ Propositional Solver
% 3.78/0.98  
% 3.78/0.98  prop_solver_calls:                      29
% 3.78/0.98  prop_fast_solver_calls:                 2208
% 3.78/0.98  smt_solver_calls:                       0
% 3.78/0.98  smt_fast_solver_calls:                  0
% 3.78/0.98  prop_num_of_clauses:                    5331
% 3.78/0.98  prop_preprocess_simplified:             13503
% 3.78/0.98  prop_fo_subsumed:                       79
% 3.78/0.98  prop_solver_time:                       0.
% 3.78/0.98  smt_solver_time:                        0.
% 3.78/0.98  smt_fast_solver_time:                   0.
% 3.78/0.98  prop_fast_solver_time:                  0.
% 3.78/0.98  prop_unsat_core_time:                   0.
% 3.78/0.98  
% 3.78/0.98  ------ QBF
% 3.78/0.98  
% 3.78/0.98  qbf_q_res:                              0
% 3.78/0.98  qbf_num_tautologies:                    0
% 3.78/0.98  qbf_prep_cycles:                        0
% 3.78/0.98  
% 3.78/0.98  ------ BMC1
% 3.78/0.98  
% 3.78/0.98  bmc1_current_bound:                     -1
% 3.78/0.98  bmc1_last_solved_bound:                 -1
% 3.78/0.98  bmc1_unsat_core_size:                   -1
% 3.78/0.98  bmc1_unsat_core_parents_size:           -1
% 3.78/0.98  bmc1_merge_next_fun:                    0
% 3.78/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.78/0.98  
% 3.78/0.98  ------ Instantiation
% 3.78/0.98  
% 3.78/0.98  inst_num_of_clauses:                    1683
% 3.78/0.98  inst_num_in_passive:                    334
% 3.78/0.98  inst_num_in_active:                     714
% 3.78/0.98  inst_num_in_unprocessed:                635
% 3.78/0.98  inst_num_of_loops:                      840
% 3.78/0.98  inst_num_of_learning_restarts:          0
% 3.78/0.98  inst_num_moves_active_passive:          123
% 3.78/0.98  inst_lit_activity:                      0
% 3.78/0.98  inst_lit_activity_moves:                0
% 3.78/0.98  inst_num_tautologies:                   0
% 3.78/0.98  inst_num_prop_implied:                  0
% 3.78/0.98  inst_num_existing_simplified:           0
% 3.78/0.98  inst_num_eq_res_simplified:             0
% 3.78/0.98  inst_num_child_elim:                    0
% 3.78/0.98  inst_num_of_dismatching_blockings:      540
% 3.78/0.98  inst_num_of_non_proper_insts:           1440
% 3.78/0.98  inst_num_of_duplicates:                 0
% 3.78/0.98  inst_inst_num_from_inst_to_res:         0
% 3.78/0.98  inst_dismatching_checking_time:         0.
% 3.78/0.98  
% 3.78/0.98  ------ Resolution
% 3.78/0.98  
% 3.78/0.98  res_num_of_clauses:                     0
% 3.78/0.98  res_num_in_passive:                     0
% 3.78/0.98  res_num_in_active:                      0
% 3.78/0.98  res_num_of_loops:                       213
% 3.78/0.98  res_forward_subset_subsumed:            69
% 3.78/0.98  res_backward_subset_subsumed:           0
% 3.78/0.98  res_forward_subsumed:                   0
% 3.78/0.98  res_backward_subsumed:                  0
% 3.78/0.98  res_forward_subsumption_resolution:     0
% 3.78/0.98  res_backward_subsumption_resolution:    0
% 3.78/0.98  res_clause_to_clause_subsumption:       947
% 3.78/0.98  res_orphan_elimination:                 0
% 3.78/0.98  res_tautology_del:                      130
% 3.78/0.98  res_num_eq_res_simplified:              0
% 3.78/0.98  res_num_sel_changes:                    0
% 3.78/0.98  res_moves_from_active_to_pass:          0
% 3.78/0.98  
% 3.78/0.98  ------ Superposition
% 3.78/0.98  
% 3.78/0.98  sup_time_total:                         0.
% 3.78/0.98  sup_time_generating:                    0.
% 3.78/0.98  sup_time_sim_full:                      0.
% 3.78/0.98  sup_time_sim_immed:                     0.
% 3.78/0.98  
% 3.78/0.98  sup_num_of_clauses:                     261
% 3.78/0.98  sup_num_in_active:                      133
% 3.78/0.98  sup_num_in_passive:                     128
% 3.78/0.98  sup_num_of_loops:                       166
% 3.78/0.98  sup_fw_superposition:                   167
% 3.78/0.98  sup_bw_superposition:                   149
% 3.78/0.98  sup_immediate_simplified:               53
% 3.78/0.98  sup_given_eliminated:                   0
% 3.78/0.98  comparisons_done:                       0
% 3.78/0.98  comparisons_avoided:                    46
% 3.78/0.98  
% 3.78/0.98  ------ Simplifications
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  sim_fw_subset_subsumed:                 26
% 3.78/0.98  sim_bw_subset_subsumed:                 0
% 3.78/0.98  sim_fw_subsumed:                        18
% 3.78/0.98  sim_bw_subsumed:                        0
% 3.78/0.98  sim_fw_subsumption_res:                 1
% 3.78/0.98  sim_bw_subsumption_res:                 0
% 3.78/0.98  sim_tautology_del:                      12
% 3.78/0.98  sim_eq_tautology_del:                   16
% 3.78/0.98  sim_eq_res_simp:                        0
% 3.78/0.98  sim_fw_demodulated:                     9
% 3.78/0.98  sim_bw_demodulated:                     33
% 3.78/0.98  sim_light_normalised:                   11
% 3.78/0.98  sim_joinable_taut:                      0
% 3.78/0.98  sim_joinable_simp:                      0
% 3.78/0.98  sim_ac_normalised:                      0
% 3.78/0.98  sim_smt_subsumption:                    0
% 3.78/0.98  
%------------------------------------------------------------------------------

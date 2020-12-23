%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:44 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 688 expanded)
%              Number of clauses        :  113 ( 210 expanded)
%              Number of leaves         :   21 ( 229 expanded)
%              Depth                    :   21
%              Number of atoms          :  689 (5198 expanded)
%              Number of equality atoms :  254 (1374 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f36,f40,f39,f38,f37])).

fof(f68,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f13,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

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

fof(f54,plain,(
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

fof(f71,plain,(
    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_638,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1062,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_645,plain,
    ( ~ m1_subset_1(X0_51,X1_51)
    | r2_hidden(X0_51,X1_51)
    | v1_xboole_0(X1_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1057,plain,
    ( m1_subset_1(X0_51,X1_51) != iProver_top
    | r2_hidden(X0_51,X1_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_1637,plain,
    ( r2_hidden(sK5,sK1) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1062,c_1057])).

cnf(c_36,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_639,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_646,plain,
    ( ~ v1_xboole_0(X0_51)
    | k1_xboole_0 = X0_51 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1278,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_646])).

cnf(c_1279,plain,
    ( k1_xboole_0 = sK1
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1278])).

cnf(c_1353,plain,
    ( ~ m1_subset_1(X0_51,sK1)
    | r2_hidden(X0_51,sK1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_1520,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | r2_hidden(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1353])).

cnf(c_1521,plain,
    ( m1_subset_1(sK5,sK1) != iProver_top
    | r2_hidden(sK5,sK1) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1520])).

cnf(c_1710,plain,
    ( r2_hidden(sK5,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1637,c_36,c_639,c_1279,c_1521])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_431,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
    | k1_relset_1(sK2,sK0,sK4) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_432,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_relset_1(sK2,sK0,sK4))))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_625,plain,
    ( ~ v1_funct_2(X0_51,X1_51,X2_51)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,k1_relset_1(sK2,sK0,sK4))))
    | ~ v1_funct_1(X0_51)
    | k2_relset_1(X1_51,X2_51,X0_51) != k2_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = X2_51 ),
    inference(subtyping,[status(esa)],[c_432])).

cnf(c_1075,plain,
    ( k2_relset_1(X0_51,X1_51,X2_51) != k2_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = X1_51
    | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,k1_relset_1(sK2,sK0,sK4)))) = iProver_top
    | v1_funct_1(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_1866,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relset_1(sK2,sK0,sK4)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1075])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_31,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_32,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_654,plain,
    ( ~ v1_xboole_0(X0_51)
    | v1_xboole_0(X1_51)
    | X1_51 != X0_51 ),
    theory(equality)).

cnf(c_1285,plain,
    ( ~ v1_xboole_0(X0_51)
    | v1_xboole_0(sK2)
    | sK2 != X0_51 ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_1287,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1285])).

cnf(c_2915,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relset_1(sK2,sK0,sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1866,c_29,c_31,c_32,c_33,c_0,c_1287])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_637,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1063,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_637])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_642,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | k1_relset_1(X1_51,X2_51,X0_51) = k1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1060,plain,
    ( k1_relset_1(X0_51,X1_51,X2_51) = k1_relat_1(X2_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_2007,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1063,c_1060])).

cnf(c_2919,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2915,c_2007])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_641,plain,
    ( ~ v1_funct_2(X0_51,X1_51,X2_51)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ r2_hidden(X3_51,X1_51)
    | r2_hidden(k1_funct_1(X0_51,X3_51),X2_51)
    | ~ v1_funct_1(X0_51)
    | k1_xboole_0 = X2_51 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1061,plain,
    ( k1_xboole_0 = X0_51
    | v1_funct_2(X1_51,X2_51,X0_51) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X0_51))) != iProver_top
    | r2_hidden(X3_51,X2_51) != iProver_top
    | r2_hidden(k1_funct_1(X1_51,X3_51),X0_51) = iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_2925,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(sK3,sK1,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X0_51,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0_51),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2919,c_1061])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_408,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
    | k1_relset_1(sK2,sK0,sK4) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_409,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,k1_relset_1(sK2,sK0,sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_626,plain,
    ( ~ v1_funct_2(X0_51,X1_51,X2_51)
    | v1_funct_2(X0_51,X1_51,k1_relset_1(sK2,sK0,sK4))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ v1_funct_1(X0_51)
    | k2_relset_1(X1_51,X2_51,X0_51) != k2_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = X2_51 ),
    inference(subtyping,[status(esa)],[c_409])).

cnf(c_1074,plain,
    ( k2_relset_1(X0_51,X1_51,X2_51) != k2_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = X1_51
    | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
    | v1_funct_2(X2_51,X0_51,k1_relset_1(sK2,sK0,sK4)) = iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_1857,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,k1_relset_1(sK2,sK0,sK4)) = iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1074])).

cnf(c_2569,plain,
    ( v1_funct_2(sK3,sK1,k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1857,c_29,c_31,c_32,c_33,c_0,c_1287])).

cnf(c_2573,plain,
    ( v1_funct_2(sK3,sK1,k1_relat_1(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2569,c_2007])).

cnf(c_3612,plain,
    ( r2_hidden(k1_funct_1(sK3,X0_51),k1_relat_1(sK4)) = iProver_top
    | r2_hidden(X0_51,sK1) != iProver_top
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2925,c_31,c_2573])).

cnf(c_3613,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | r2_hidden(X0_51,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0_51),k1_relat_1(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3612])).

cnf(c_5,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_302,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_5,c_11])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_306,plain,
    ( ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_302,c_4])).

cnf(c_307,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(renaming,[status(thm)],[c_306])).

cnf(c_630,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ r2_hidden(X3_51,k1_relat_1(X0_51))
    | ~ v1_funct_1(X0_51)
    | k7_partfun1(X2_51,X0_51,X3_51) = k1_funct_1(X0_51,X3_51) ),
    inference(subtyping,[status(esa)],[c_307])).

cnf(c_1070,plain,
    ( k7_partfun1(X0_51,X1_51,X2_51) = k1_funct_1(X1_51,X2_51)
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X3_51,X0_51))) != iProver_top
    | r2_hidden(X2_51,k1_relat_1(X1_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_3357,plain,
    ( k7_partfun1(sK0,sK4,X0_51) = k1_funct_1(sK4,X0_51)
    | r2_hidden(X0_51,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1063,c_1070])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_34,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3417,plain,
    ( r2_hidden(X0_51,k1_relat_1(sK4)) != iProver_top
    | k7_partfun1(sK0,sK4,X0_51) = k1_funct_1(sK4,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3357,c_34])).

cnf(c_3418,plain,
    ( k7_partfun1(sK0,sK4,X0_51) = k1_funct_1(sK4,X0_51)
    | r2_hidden(X0_51,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3417])).

cnf(c_3621,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0_51)) = k1_funct_1(sK4,k1_funct_1(sK3,X0_51))
    | k1_relat_1(sK4) = k1_xboole_0
    | r2_hidden(X0_51,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3613,c_3418])).

cnf(c_3629,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1710,c_3621])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f54])).

cnf(c_330,plain,
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
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_629,plain,
    ( ~ v1_funct_2(X0_51,X1_51,X2_51)
    | ~ m1_subset_1(X3_51,X1_51)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X5_51)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X4_51)
    | v1_xboole_0(X2_51)
    | k2_relset_1(X1_51,X2_51,X0_51) != k2_relset_1(sK1,sK2,sK3)
    | k1_relset_1(X2_51,X5_51,X4_51) != k1_relset_1(sK2,sK0,sK4)
    | k1_funct_1(k8_funct_2(X1_51,X2_51,X5_51,X0_51,X4_51),X3_51) = k1_funct_1(X4_51,k1_funct_1(X0_51,X3_51))
    | k1_xboole_0 = X1_51 ),
    inference(subtyping,[status(esa)],[c_330])).

cnf(c_1071,plain,
    ( k2_relset_1(X0_51,X1_51,X2_51) != k2_relset_1(sK1,sK2,sK3)
    | k1_relset_1(X1_51,X3_51,X4_51) != k1_relset_1(sK2,sK0,sK4)
    | k1_funct_1(k8_funct_2(X0_51,X1_51,X3_51,X2_51,X4_51),X5_51) = k1_funct_1(X4_51,k1_funct_1(X2_51,X5_51))
    | k1_xboole_0 = X0_51
    | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
    | m1_subset_1(X5_51,X0_51) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X3_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_funct_1(X4_51) != iProver_top
    | v1_xboole_0(X1_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_1967,plain,
    ( k1_relset_1(sK2,X0_51,X1_51) != k1_relset_1(sK2,sK0,sK4)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0_51,sK3,X1_51),X2_51) = k1_funct_1(X1_51,k1_funct_1(sK3,X2_51))
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51))) != iProver_top
    | m1_subset_1(X2_51,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1071])).

cnf(c_30,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_649,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_679,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_649])).

cnf(c_652,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_1300,plain,
    ( sK1 != X0_51
    | k1_xboole_0 != X0_51
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_652])).

cnf(c_1301,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1300])).

cnf(c_2953,plain,
    ( m1_subset_1(X2_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51))) != iProver_top
    | k1_funct_1(k8_funct_2(sK1,sK2,X0_51,sK3,X1_51),X2_51) = k1_funct_1(X1_51,k1_funct_1(sK3,X2_51))
    | k1_relset_1(sK2,X0_51,X1_51) != k1_relset_1(sK2,sK0,sK4)
    | v1_funct_1(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1967,c_30,c_31,c_32,c_33,c_679,c_639,c_1301])).

cnf(c_2954,plain,
    ( k1_relset_1(sK2,X0_51,X1_51) != k1_relset_1(sK2,sK0,sK4)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0_51,sK3,X1_51),X2_51) = k1_funct_1(X1_51,k1_funct_1(sK3,X2_51))
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51))) != iProver_top
    | m1_subset_1(X2_51,sK1) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_2953])).

cnf(c_2959,plain,
    ( k1_relset_1(sK2,X0_51,X1_51) != k1_relat_1(sK4)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0_51,sK3,X1_51),X2_51) = k1_funct_1(X1_51,k1_funct_1(sK3,X2_51))
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51))) != iProver_top
    | m1_subset_1(X2_51,sK1) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2954,c_2007])).

cnf(c_2968,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0_51) = k1_funct_1(sK4,k1_funct_1(sK3,X0_51))
    | m1_subset_1(X0_51,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2007,c_2959])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3069,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0_51) = k1_funct_1(sK4,k1_funct_1(sK3,X0_51))
    | m1_subset_1(X0_51,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2968,c_34,c_35])).

cnf(c_3077,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1062,c_3069])).

cnf(c_20,negated_conjecture,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_640,negated_conjecture,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_3079,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_3077,c_640])).

cnf(c_3680,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3629,c_3079])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_643,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ v1_xboole_0(X2_51)
    | v1_xboole_0(X0_51) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1059,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | v1_xboole_0(X2_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_643])).

cnf(c_2923,plain,
    ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2919,c_1059])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_148,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_3])).

cnf(c_149,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(renaming,[status(thm)],[c_148])).

cnf(c_631,plain,
    ( ~ v1_funct_2(X0_51,X1_51,X2_51)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ v1_xboole_0(X0_51)
    | v1_xboole_0(X2_51)
    | v1_xboole_0(X1_51) ),
    inference(subtyping,[status(esa)],[c_149])).

cnf(c_1327,plain,
    ( ~ v1_funct_2(X0_51,X1_51,sK2)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK2)))
    | ~ v1_xboole_0(X0_51)
    | v1_xboole_0(X1_51)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_631])).

cnf(c_1462,plain,
    ( ~ v1_funct_2(X0_51,sK1,sK2)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_xboole_0(X0_51)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1327])).

cnf(c_1832,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1462])).

cnf(c_1833,plain,
    ( v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1832])).

cnf(c_3324,plain,
    ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2923,c_30,c_32,c_33,c_639,c_1279,c_1833])).

cnf(c_3686,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3680,c_3324])).

cnf(c_75,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3686,c_75])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:52:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.22/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.00  
% 2.22/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.22/1.00  
% 2.22/1.00  ------  iProver source info
% 2.22/1.00  
% 2.22/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.22/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.22/1.00  git: non_committed_changes: false
% 2.22/1.00  git: last_make_outside_of_git: false
% 2.22/1.00  
% 2.22/1.00  ------ 
% 2.22/1.00  
% 2.22/1.00  ------ Input Options
% 2.22/1.00  
% 2.22/1.00  --out_options                           all
% 2.22/1.00  --tptp_safe_out                         true
% 2.22/1.00  --problem_path                          ""
% 2.22/1.00  --include_path                          ""
% 2.22/1.00  --clausifier                            res/vclausify_rel
% 2.22/1.00  --clausifier_options                    --mode clausify
% 2.22/1.00  --stdin                                 false
% 2.22/1.00  --stats_out                             all
% 2.22/1.00  
% 2.22/1.00  ------ General Options
% 2.22/1.00  
% 2.22/1.00  --fof                                   false
% 2.22/1.00  --time_out_real                         305.
% 2.22/1.00  --time_out_virtual                      -1.
% 2.22/1.00  --symbol_type_check                     false
% 2.22/1.00  --clausify_out                          false
% 2.22/1.00  --sig_cnt_out                           false
% 2.22/1.00  --trig_cnt_out                          false
% 2.22/1.00  --trig_cnt_out_tolerance                1.
% 2.22/1.00  --trig_cnt_out_sk_spl                   false
% 2.22/1.00  --abstr_cl_out                          false
% 2.22/1.00  
% 2.22/1.00  ------ Global Options
% 2.22/1.00  
% 2.22/1.00  --schedule                              default
% 2.22/1.00  --add_important_lit                     false
% 2.22/1.00  --prop_solver_per_cl                    1000
% 2.22/1.00  --min_unsat_core                        false
% 2.22/1.00  --soft_assumptions                      false
% 2.22/1.00  --soft_lemma_size                       3
% 2.22/1.00  --prop_impl_unit_size                   0
% 2.22/1.00  --prop_impl_unit                        []
% 2.22/1.00  --share_sel_clauses                     true
% 2.22/1.00  --reset_solvers                         false
% 2.22/1.00  --bc_imp_inh                            [conj_cone]
% 2.22/1.00  --conj_cone_tolerance                   3.
% 2.22/1.00  --extra_neg_conj                        none
% 2.22/1.00  --large_theory_mode                     true
% 2.22/1.00  --prolific_symb_bound                   200
% 2.22/1.00  --lt_threshold                          2000
% 2.22/1.00  --clause_weak_htbl                      true
% 2.22/1.00  --gc_record_bc_elim                     false
% 2.22/1.00  
% 2.22/1.00  ------ Preprocessing Options
% 2.22/1.00  
% 2.22/1.00  --preprocessing_flag                    true
% 2.22/1.00  --time_out_prep_mult                    0.1
% 2.22/1.00  --splitting_mode                        input
% 2.22/1.00  --splitting_grd                         true
% 2.22/1.00  --splitting_cvd                         false
% 2.22/1.00  --splitting_cvd_svl                     false
% 2.22/1.00  --splitting_nvd                         32
% 2.22/1.00  --sub_typing                            true
% 2.22/1.00  --prep_gs_sim                           true
% 2.22/1.00  --prep_unflatten                        true
% 2.22/1.00  --prep_res_sim                          true
% 2.22/1.00  --prep_upred                            true
% 2.22/1.00  --prep_sem_filter                       exhaustive
% 2.22/1.00  --prep_sem_filter_out                   false
% 2.22/1.00  --pred_elim                             true
% 2.22/1.00  --res_sim_input                         true
% 2.22/1.00  --eq_ax_congr_red                       true
% 2.22/1.00  --pure_diseq_elim                       true
% 2.22/1.00  --brand_transform                       false
% 2.22/1.00  --non_eq_to_eq                          false
% 2.22/1.00  --prep_def_merge                        true
% 2.22/1.00  --prep_def_merge_prop_impl              false
% 2.22/1.00  --prep_def_merge_mbd                    true
% 2.22/1.00  --prep_def_merge_tr_red                 false
% 2.22/1.00  --prep_def_merge_tr_cl                  false
% 2.22/1.00  --smt_preprocessing                     true
% 2.22/1.00  --smt_ac_axioms                         fast
% 2.22/1.00  --preprocessed_out                      false
% 2.22/1.00  --preprocessed_stats                    false
% 2.22/1.00  
% 2.22/1.00  ------ Abstraction refinement Options
% 2.22/1.00  
% 2.22/1.00  --abstr_ref                             []
% 2.22/1.00  --abstr_ref_prep                        false
% 2.22/1.00  --abstr_ref_until_sat                   false
% 2.22/1.00  --abstr_ref_sig_restrict                funpre
% 2.22/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/1.00  --abstr_ref_under                       []
% 2.22/1.00  
% 2.22/1.00  ------ SAT Options
% 2.22/1.00  
% 2.22/1.00  --sat_mode                              false
% 2.22/1.00  --sat_fm_restart_options                ""
% 2.22/1.00  --sat_gr_def                            false
% 2.22/1.00  --sat_epr_types                         true
% 2.22/1.00  --sat_non_cyclic_types                  false
% 2.22/1.00  --sat_finite_models                     false
% 2.22/1.00  --sat_fm_lemmas                         false
% 2.22/1.00  --sat_fm_prep                           false
% 2.22/1.00  --sat_fm_uc_incr                        true
% 2.22/1.00  --sat_out_model                         small
% 2.22/1.00  --sat_out_clauses                       false
% 2.22/1.00  
% 2.22/1.00  ------ QBF Options
% 2.22/1.00  
% 2.22/1.00  --qbf_mode                              false
% 2.22/1.00  --qbf_elim_univ                         false
% 2.22/1.00  --qbf_dom_inst                          none
% 2.22/1.00  --qbf_dom_pre_inst                      false
% 2.22/1.00  --qbf_sk_in                             false
% 2.22/1.00  --qbf_pred_elim                         true
% 2.22/1.00  --qbf_split                             512
% 2.22/1.00  
% 2.22/1.00  ------ BMC1 Options
% 2.22/1.00  
% 2.22/1.00  --bmc1_incremental                      false
% 2.22/1.00  --bmc1_axioms                           reachable_all
% 2.22/1.00  --bmc1_min_bound                        0
% 2.22/1.00  --bmc1_max_bound                        -1
% 2.22/1.00  --bmc1_max_bound_default                -1
% 2.22/1.00  --bmc1_symbol_reachability              true
% 2.22/1.00  --bmc1_property_lemmas                  false
% 2.22/1.00  --bmc1_k_induction                      false
% 2.22/1.00  --bmc1_non_equiv_states                 false
% 2.22/1.00  --bmc1_deadlock                         false
% 2.22/1.00  --bmc1_ucm                              false
% 2.22/1.00  --bmc1_add_unsat_core                   none
% 2.22/1.00  --bmc1_unsat_core_children              false
% 2.22/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/1.00  --bmc1_out_stat                         full
% 2.22/1.00  --bmc1_ground_init                      false
% 2.22/1.00  --bmc1_pre_inst_next_state              false
% 2.22/1.00  --bmc1_pre_inst_state                   false
% 2.22/1.00  --bmc1_pre_inst_reach_state             false
% 2.22/1.00  --bmc1_out_unsat_core                   false
% 2.22/1.00  --bmc1_aig_witness_out                  false
% 2.22/1.00  --bmc1_verbose                          false
% 2.22/1.00  --bmc1_dump_clauses_tptp                false
% 2.22/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.22/1.00  --bmc1_dump_file                        -
% 2.22/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.22/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.22/1.00  --bmc1_ucm_extend_mode                  1
% 2.22/1.00  --bmc1_ucm_init_mode                    2
% 2.22/1.00  --bmc1_ucm_cone_mode                    none
% 2.22/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.22/1.00  --bmc1_ucm_relax_model                  4
% 2.22/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.22/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/1.00  --bmc1_ucm_layered_model                none
% 2.22/1.00  --bmc1_ucm_max_lemma_size               10
% 2.22/1.00  
% 2.22/1.00  ------ AIG Options
% 2.22/1.00  
% 2.22/1.00  --aig_mode                              false
% 2.22/1.00  
% 2.22/1.00  ------ Instantiation Options
% 2.22/1.00  
% 2.22/1.00  --instantiation_flag                    true
% 2.22/1.00  --inst_sos_flag                         false
% 2.22/1.00  --inst_sos_phase                        true
% 2.22/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/1.00  --inst_lit_sel_side                     num_symb
% 2.22/1.00  --inst_solver_per_active                1400
% 2.22/1.00  --inst_solver_calls_frac                1.
% 2.22/1.00  --inst_passive_queue_type               priority_queues
% 2.22/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/1.00  --inst_passive_queues_freq              [25;2]
% 2.22/1.00  --inst_dismatching                      true
% 2.22/1.00  --inst_eager_unprocessed_to_passive     true
% 2.22/1.00  --inst_prop_sim_given                   true
% 2.22/1.00  --inst_prop_sim_new                     false
% 2.22/1.00  --inst_subs_new                         false
% 2.22/1.00  --inst_eq_res_simp                      false
% 2.22/1.00  --inst_subs_given                       false
% 2.22/1.00  --inst_orphan_elimination               true
% 2.22/1.00  --inst_learning_loop_flag               true
% 2.22/1.00  --inst_learning_start                   3000
% 2.22/1.00  --inst_learning_factor                  2
% 2.22/1.00  --inst_start_prop_sim_after_learn       3
% 2.22/1.00  --inst_sel_renew                        solver
% 2.22/1.00  --inst_lit_activity_flag                true
% 2.22/1.00  --inst_restr_to_given                   false
% 2.22/1.00  --inst_activity_threshold               500
% 2.22/1.00  --inst_out_proof                        true
% 2.22/1.00  
% 2.22/1.00  ------ Resolution Options
% 2.22/1.00  
% 2.22/1.00  --resolution_flag                       true
% 2.22/1.00  --res_lit_sel                           adaptive
% 2.22/1.00  --res_lit_sel_side                      none
% 2.22/1.00  --res_ordering                          kbo
% 2.22/1.00  --res_to_prop_solver                    active
% 2.22/1.00  --res_prop_simpl_new                    false
% 2.22/1.00  --res_prop_simpl_given                  true
% 2.22/1.00  --res_passive_queue_type                priority_queues
% 2.22/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/1.00  --res_passive_queues_freq               [15;5]
% 2.22/1.00  --res_forward_subs                      full
% 2.22/1.00  --res_backward_subs                     full
% 2.22/1.00  --res_forward_subs_resolution           true
% 2.22/1.00  --res_backward_subs_resolution          true
% 2.22/1.00  --res_orphan_elimination                true
% 2.22/1.00  --res_time_limit                        2.
% 2.22/1.00  --res_out_proof                         true
% 2.22/1.00  
% 2.22/1.00  ------ Superposition Options
% 2.22/1.00  
% 2.22/1.00  --superposition_flag                    true
% 2.22/1.00  --sup_passive_queue_type                priority_queues
% 2.22/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.22/1.00  --demod_completeness_check              fast
% 2.22/1.00  --demod_use_ground                      true
% 2.22/1.00  --sup_to_prop_solver                    passive
% 2.22/1.00  --sup_prop_simpl_new                    true
% 2.22/1.00  --sup_prop_simpl_given                  true
% 2.22/1.00  --sup_fun_splitting                     false
% 2.22/1.00  --sup_smt_interval                      50000
% 2.22/1.00  
% 2.22/1.00  ------ Superposition Simplification Setup
% 2.22/1.00  
% 2.22/1.00  --sup_indices_passive                   []
% 2.22/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.00  --sup_full_bw                           [BwDemod]
% 2.22/1.00  --sup_immed_triv                        [TrivRules]
% 2.22/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.00  --sup_immed_bw_main                     []
% 2.22/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.00  
% 2.22/1.00  ------ Combination Options
% 2.22/1.00  
% 2.22/1.00  --comb_res_mult                         3
% 2.22/1.00  --comb_sup_mult                         2
% 2.22/1.00  --comb_inst_mult                        10
% 2.22/1.00  
% 2.22/1.00  ------ Debug Options
% 2.22/1.00  
% 2.22/1.00  --dbg_backtrace                         false
% 2.22/1.00  --dbg_dump_prop_clauses                 false
% 2.22/1.00  --dbg_dump_prop_clauses_file            -
% 2.22/1.00  --dbg_out_stat                          false
% 2.22/1.00  ------ Parsing...
% 2.22/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.22/1.00  
% 2.22/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.22/1.00  
% 2.22/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.22/1.00  
% 2.22/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.22/1.00  ------ Proving...
% 2.22/1.00  ------ Problem Properties 
% 2.22/1.00  
% 2.22/1.00  
% 2.22/1.00  clauses                                 23
% 2.22/1.00  conjectures                             9
% 2.22/1.00  EPR                                     10
% 2.22/1.00  Horn                                    17
% 2.22/1.00  unary                                   10
% 2.22/1.00  binary                                  3
% 2.22/1.00  lits                                    70
% 2.22/1.00  lits eq                                 16
% 2.22/1.00  fd_pure                                 0
% 2.22/1.00  fd_pseudo                               0
% 2.22/1.00  fd_cond                                 5
% 2.22/1.00  fd_pseudo_cond                          0
% 2.22/1.00  AC symbols                              0
% 2.22/1.00  
% 2.22/1.00  ------ Schedule dynamic 5 is on 
% 2.22/1.00  
% 2.22/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.22/1.00  
% 2.22/1.00  
% 2.22/1.00  ------ 
% 2.22/1.00  Current options:
% 2.22/1.00  ------ 
% 2.22/1.00  
% 2.22/1.00  ------ Input Options
% 2.22/1.00  
% 2.22/1.00  --out_options                           all
% 2.22/1.00  --tptp_safe_out                         true
% 2.22/1.00  --problem_path                          ""
% 2.22/1.00  --include_path                          ""
% 2.22/1.00  --clausifier                            res/vclausify_rel
% 2.22/1.00  --clausifier_options                    --mode clausify
% 2.22/1.00  --stdin                                 false
% 2.22/1.00  --stats_out                             all
% 2.22/1.00  
% 2.22/1.00  ------ General Options
% 2.22/1.00  
% 2.22/1.00  --fof                                   false
% 2.22/1.00  --time_out_real                         305.
% 2.22/1.00  --time_out_virtual                      -1.
% 2.22/1.00  --symbol_type_check                     false
% 2.22/1.00  --clausify_out                          false
% 2.22/1.00  --sig_cnt_out                           false
% 2.22/1.00  --trig_cnt_out                          false
% 2.22/1.00  --trig_cnt_out_tolerance                1.
% 2.22/1.00  --trig_cnt_out_sk_spl                   false
% 2.22/1.00  --abstr_cl_out                          false
% 2.22/1.00  
% 2.22/1.00  ------ Global Options
% 2.22/1.00  
% 2.22/1.00  --schedule                              default
% 2.22/1.00  --add_important_lit                     false
% 2.22/1.00  --prop_solver_per_cl                    1000
% 2.22/1.00  --min_unsat_core                        false
% 2.22/1.00  --soft_assumptions                      false
% 2.22/1.00  --soft_lemma_size                       3
% 2.22/1.00  --prop_impl_unit_size                   0
% 2.22/1.00  --prop_impl_unit                        []
% 2.22/1.00  --share_sel_clauses                     true
% 2.22/1.00  --reset_solvers                         false
% 2.22/1.00  --bc_imp_inh                            [conj_cone]
% 2.22/1.00  --conj_cone_tolerance                   3.
% 2.22/1.00  --extra_neg_conj                        none
% 2.22/1.00  --large_theory_mode                     true
% 2.22/1.00  --prolific_symb_bound                   200
% 2.22/1.00  --lt_threshold                          2000
% 2.22/1.00  --clause_weak_htbl                      true
% 2.22/1.00  --gc_record_bc_elim                     false
% 2.22/1.00  
% 2.22/1.00  ------ Preprocessing Options
% 2.22/1.00  
% 2.22/1.00  --preprocessing_flag                    true
% 2.22/1.00  --time_out_prep_mult                    0.1
% 2.22/1.00  --splitting_mode                        input
% 2.22/1.00  --splitting_grd                         true
% 2.22/1.00  --splitting_cvd                         false
% 2.22/1.00  --splitting_cvd_svl                     false
% 2.22/1.00  --splitting_nvd                         32
% 2.22/1.00  --sub_typing                            true
% 2.22/1.00  --prep_gs_sim                           true
% 2.22/1.00  --prep_unflatten                        true
% 2.22/1.00  --prep_res_sim                          true
% 2.22/1.00  --prep_upred                            true
% 2.22/1.00  --prep_sem_filter                       exhaustive
% 2.22/1.00  --prep_sem_filter_out                   false
% 2.22/1.00  --pred_elim                             true
% 2.22/1.00  --res_sim_input                         true
% 2.22/1.00  --eq_ax_congr_red                       true
% 2.22/1.00  --pure_diseq_elim                       true
% 2.22/1.00  --brand_transform                       false
% 2.22/1.00  --non_eq_to_eq                          false
% 2.22/1.00  --prep_def_merge                        true
% 2.22/1.00  --prep_def_merge_prop_impl              false
% 2.22/1.00  --prep_def_merge_mbd                    true
% 2.22/1.00  --prep_def_merge_tr_red                 false
% 2.22/1.00  --prep_def_merge_tr_cl                  false
% 2.22/1.00  --smt_preprocessing                     true
% 2.22/1.00  --smt_ac_axioms                         fast
% 2.22/1.00  --preprocessed_out                      false
% 2.22/1.00  --preprocessed_stats                    false
% 2.22/1.00  
% 2.22/1.00  ------ Abstraction refinement Options
% 2.22/1.00  
% 2.22/1.00  --abstr_ref                             []
% 2.22/1.00  --abstr_ref_prep                        false
% 2.22/1.00  --abstr_ref_until_sat                   false
% 2.22/1.00  --abstr_ref_sig_restrict                funpre
% 2.22/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/1.00  --abstr_ref_under                       []
% 2.22/1.00  
% 2.22/1.00  ------ SAT Options
% 2.22/1.00  
% 2.22/1.00  --sat_mode                              false
% 2.22/1.00  --sat_fm_restart_options                ""
% 2.22/1.00  --sat_gr_def                            false
% 2.22/1.00  --sat_epr_types                         true
% 2.22/1.00  --sat_non_cyclic_types                  false
% 2.22/1.00  --sat_finite_models                     false
% 2.22/1.00  --sat_fm_lemmas                         false
% 2.22/1.00  --sat_fm_prep                           false
% 2.22/1.00  --sat_fm_uc_incr                        true
% 2.22/1.00  --sat_out_model                         small
% 2.22/1.00  --sat_out_clauses                       false
% 2.22/1.00  
% 2.22/1.00  ------ QBF Options
% 2.22/1.00  
% 2.22/1.00  --qbf_mode                              false
% 2.22/1.00  --qbf_elim_univ                         false
% 2.22/1.00  --qbf_dom_inst                          none
% 2.22/1.00  --qbf_dom_pre_inst                      false
% 2.22/1.00  --qbf_sk_in                             false
% 2.22/1.00  --qbf_pred_elim                         true
% 2.22/1.00  --qbf_split                             512
% 2.22/1.00  
% 2.22/1.00  ------ BMC1 Options
% 2.22/1.00  
% 2.22/1.00  --bmc1_incremental                      false
% 2.22/1.00  --bmc1_axioms                           reachable_all
% 2.22/1.00  --bmc1_min_bound                        0
% 2.22/1.00  --bmc1_max_bound                        -1
% 2.22/1.00  --bmc1_max_bound_default                -1
% 2.22/1.00  --bmc1_symbol_reachability              true
% 2.22/1.00  --bmc1_property_lemmas                  false
% 2.22/1.00  --bmc1_k_induction                      false
% 2.22/1.00  --bmc1_non_equiv_states                 false
% 2.22/1.00  --bmc1_deadlock                         false
% 2.22/1.00  --bmc1_ucm                              false
% 2.22/1.00  --bmc1_add_unsat_core                   none
% 2.22/1.00  --bmc1_unsat_core_children              false
% 2.22/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/1.00  --bmc1_out_stat                         full
% 2.22/1.00  --bmc1_ground_init                      false
% 2.22/1.00  --bmc1_pre_inst_next_state              false
% 2.22/1.00  --bmc1_pre_inst_state                   false
% 2.22/1.00  --bmc1_pre_inst_reach_state             false
% 2.22/1.00  --bmc1_out_unsat_core                   false
% 2.22/1.00  --bmc1_aig_witness_out                  false
% 2.22/1.00  --bmc1_verbose                          false
% 2.22/1.00  --bmc1_dump_clauses_tptp                false
% 2.22/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.22/1.00  --bmc1_dump_file                        -
% 2.22/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.22/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.22/1.00  --bmc1_ucm_extend_mode                  1
% 2.22/1.00  --bmc1_ucm_init_mode                    2
% 2.22/1.00  --bmc1_ucm_cone_mode                    none
% 2.22/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.22/1.00  --bmc1_ucm_relax_model                  4
% 2.22/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.22/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/1.00  --bmc1_ucm_layered_model                none
% 2.22/1.00  --bmc1_ucm_max_lemma_size               10
% 2.22/1.00  
% 2.22/1.00  ------ AIG Options
% 2.22/1.00  
% 2.22/1.00  --aig_mode                              false
% 2.22/1.00  
% 2.22/1.00  ------ Instantiation Options
% 2.22/1.00  
% 2.22/1.00  --instantiation_flag                    true
% 2.22/1.00  --inst_sos_flag                         false
% 2.22/1.00  --inst_sos_phase                        true
% 2.22/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/1.00  --inst_lit_sel_side                     none
% 2.22/1.00  --inst_solver_per_active                1400
% 2.22/1.00  --inst_solver_calls_frac                1.
% 2.22/1.00  --inst_passive_queue_type               priority_queues
% 2.22/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/1.00  --inst_passive_queues_freq              [25;2]
% 2.22/1.00  --inst_dismatching                      true
% 2.22/1.00  --inst_eager_unprocessed_to_passive     true
% 2.22/1.00  --inst_prop_sim_given                   true
% 2.22/1.00  --inst_prop_sim_new                     false
% 2.22/1.00  --inst_subs_new                         false
% 2.22/1.00  --inst_eq_res_simp                      false
% 2.22/1.00  --inst_subs_given                       false
% 2.22/1.00  --inst_orphan_elimination               true
% 2.22/1.00  --inst_learning_loop_flag               true
% 2.22/1.00  --inst_learning_start                   3000
% 2.22/1.00  --inst_learning_factor                  2
% 2.22/1.00  --inst_start_prop_sim_after_learn       3
% 2.22/1.00  --inst_sel_renew                        solver
% 2.22/1.00  --inst_lit_activity_flag                true
% 2.22/1.00  --inst_restr_to_given                   false
% 2.22/1.00  --inst_activity_threshold               500
% 2.22/1.00  --inst_out_proof                        true
% 2.22/1.00  
% 2.22/1.00  ------ Resolution Options
% 2.22/1.00  
% 2.22/1.00  --resolution_flag                       false
% 2.22/1.00  --res_lit_sel                           adaptive
% 2.22/1.00  --res_lit_sel_side                      none
% 2.22/1.00  --res_ordering                          kbo
% 2.22/1.00  --res_to_prop_solver                    active
% 2.22/1.00  --res_prop_simpl_new                    false
% 2.22/1.00  --res_prop_simpl_given                  true
% 2.22/1.00  --res_passive_queue_type                priority_queues
% 2.22/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/1.00  --res_passive_queues_freq               [15;5]
% 2.22/1.00  --res_forward_subs                      full
% 2.22/1.00  --res_backward_subs                     full
% 2.22/1.00  --res_forward_subs_resolution           true
% 2.22/1.00  --res_backward_subs_resolution          true
% 2.22/1.00  --res_orphan_elimination                true
% 2.22/1.00  --res_time_limit                        2.
% 2.22/1.00  --res_out_proof                         true
% 2.22/1.00  
% 2.22/1.00  ------ Superposition Options
% 2.22/1.00  
% 2.22/1.00  --superposition_flag                    true
% 2.22/1.00  --sup_passive_queue_type                priority_queues
% 2.22/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.22/1.00  --demod_completeness_check              fast
% 2.22/1.00  --demod_use_ground                      true
% 2.22/1.00  --sup_to_prop_solver                    passive
% 2.22/1.00  --sup_prop_simpl_new                    true
% 2.22/1.00  --sup_prop_simpl_given                  true
% 2.22/1.00  --sup_fun_splitting                     false
% 2.22/1.00  --sup_smt_interval                      50000
% 2.22/1.00  
% 2.22/1.00  ------ Superposition Simplification Setup
% 2.22/1.00  
% 2.22/1.00  --sup_indices_passive                   []
% 2.22/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.00  --sup_full_bw                           [BwDemod]
% 2.22/1.00  --sup_immed_triv                        [TrivRules]
% 2.22/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.00  --sup_immed_bw_main                     []
% 2.22/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.00  
% 2.22/1.00  ------ Combination Options
% 2.22/1.00  
% 2.22/1.00  --comb_res_mult                         3
% 2.22/1.00  --comb_sup_mult                         2
% 2.22/1.00  --comb_inst_mult                        10
% 2.22/1.00  
% 2.22/1.00  ------ Debug Options
% 2.22/1.00  
% 2.22/1.00  --dbg_backtrace                         false
% 2.22/1.00  --dbg_dump_prop_clauses                 false
% 2.22/1.00  --dbg_dump_prop_clauses_file            -
% 2.22/1.00  --dbg_out_stat                          false
% 2.22/1.00  
% 2.22/1.00  
% 2.22/1.00  
% 2.22/1.00  
% 2.22/1.00  ------ Proving...
% 2.22/1.00  
% 2.22/1.00  
% 2.22/1.00  % SZS status Theorem for theBenchmark.p
% 2.22/1.00  
% 2.22/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.22/1.00  
% 2.22/1.00  fof(f14,conjecture,(
% 2.22/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f15,negated_conjecture,(
% 2.22/1.00    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.22/1.00    inference(negated_conjecture,[],[f14])).
% 2.22/1.00  
% 2.22/1.00  fof(f35,plain,(
% 2.22/1.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 2.22/1.00    inference(ennf_transformation,[],[f15])).
% 2.22/1.00  
% 2.22/1.00  fof(f36,plain,(
% 2.22/1.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 2.22/1.00    inference(flattening,[],[f35])).
% 2.22/1.00  
% 2.22/1.00  fof(f40,plain,(
% 2.22/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k7_partfun1(X0,X4,k1_funct_1(X3,sK5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK5,X1))) )),
% 2.22/1.00    introduced(choice_axiom,[])).
% 2.22/1.00  
% 2.22/1.00  fof(f39,plain,(
% 2.22/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k7_partfun1(X0,sK4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4)) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK4))) )),
% 2.22/1.00    introduced(choice_axiom,[])).
% 2.22/1.00  
% 2.22/1.00  fof(f38,plain,(
% 2.22/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(sK3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK3,X1,X2) & v1_funct_1(sK3))) )),
% 2.22/1.00    introduced(choice_axiom,[])).
% 2.22/1.00  
% 2.22/1.00  fof(f37,plain,(
% 2.22/1.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 2.22/1.00    introduced(choice_axiom,[])).
% 2.22/1.00  
% 2.22/1.00  fof(f41,plain,(
% 2.22/1.00    (((k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 2.22/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f36,f40,f39,f38,f37])).
% 2.22/1.00  
% 2.22/1.00  fof(f68,plain,(
% 2.22/1.00    m1_subset_1(sK5,sK1)),
% 2.22/1.00    inference(cnf_transformation,[],[f41])).
% 2.22/1.00  
% 2.22/1.00  fof(f3,axiom,(
% 2.22/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f18,plain,(
% 2.22/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.22/1.00    inference(ennf_transformation,[],[f3])).
% 2.22/1.00  
% 2.22/1.00  fof(f19,plain,(
% 2.22/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.22/1.00    inference(flattening,[],[f18])).
% 2.22/1.00  
% 2.22/1.00  fof(f44,plain,(
% 2.22/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f19])).
% 2.22/1.00  
% 2.22/1.00  fof(f70,plain,(
% 2.22/1.00    k1_xboole_0 != sK1),
% 2.22/1.00    inference(cnf_transformation,[],[f41])).
% 2.22/1.00  
% 2.22/1.00  fof(f2,axiom,(
% 2.22/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f17,plain,(
% 2.22/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.22/1.00    inference(ennf_transformation,[],[f2])).
% 2.22/1.00  
% 2.22/1.00  fof(f43,plain,(
% 2.22/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f17])).
% 2.22/1.00  
% 2.22/1.00  fof(f13,axiom,(
% 2.22/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f33,plain,(
% 2.22/1.00    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.22/1.00    inference(ennf_transformation,[],[f13])).
% 2.22/1.00  
% 2.22/1.00  fof(f34,plain,(
% 2.22/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.22/1.00    inference(flattening,[],[f33])).
% 2.22/1.00  
% 2.22/1.00  fof(f60,plain,(
% 2.22/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f34])).
% 2.22/1.00  
% 2.22/1.00  fof(f69,plain,(
% 2.22/1.00    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 2.22/1.00    inference(cnf_transformation,[],[f41])).
% 2.22/1.00  
% 2.22/1.00  fof(f62,plain,(
% 2.22/1.00    ~v1_xboole_0(sK2)),
% 2.22/1.00    inference(cnf_transformation,[],[f41])).
% 2.22/1.00  
% 2.22/1.00  fof(f63,plain,(
% 2.22/1.00    v1_funct_1(sK3)),
% 2.22/1.00    inference(cnf_transformation,[],[f41])).
% 2.22/1.00  
% 2.22/1.00  fof(f64,plain,(
% 2.22/1.00    v1_funct_2(sK3,sK1,sK2)),
% 2.22/1.00    inference(cnf_transformation,[],[f41])).
% 2.22/1.00  
% 2.22/1.00  fof(f65,plain,(
% 2.22/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.22/1.00    inference(cnf_transformation,[],[f41])).
% 2.22/1.00  
% 2.22/1.00  fof(f1,axiom,(
% 2.22/1.00    v1_xboole_0(k1_xboole_0)),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f42,plain,(
% 2.22/1.00    v1_xboole_0(k1_xboole_0)),
% 2.22/1.00    inference(cnf_transformation,[],[f1])).
% 2.22/1.00  
% 2.22/1.00  fof(f67,plain,(
% 2.22/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 2.22/1.00    inference(cnf_transformation,[],[f41])).
% 2.22/1.00  
% 2.22/1.00  fof(f8,axiom,(
% 2.22/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f24,plain,(
% 2.22/1.00    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/1.00    inference(ennf_transformation,[],[f8])).
% 2.22/1.00  
% 2.22/1.00  fof(f49,plain,(
% 2.22/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/1.00    inference(cnf_transformation,[],[f24])).
% 2.22/1.00  
% 2.22/1.00  fof(f12,axiom,(
% 2.22/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f31,plain,(
% 2.22/1.00    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.22/1.00    inference(ennf_transformation,[],[f12])).
% 2.22/1.00  
% 2.22/1.00  fof(f32,plain,(
% 2.22/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.22/1.00    inference(flattening,[],[f31])).
% 2.22/1.00  
% 2.22/1.00  fof(f55,plain,(
% 2.22/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f32])).
% 2.22/1.00  
% 2.22/1.00  fof(f58,plain,(
% 2.22/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f34])).
% 2.22/1.00  
% 2.22/1.00  fof(f6,axiom,(
% 2.22/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f16,plain,(
% 2.22/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.22/1.00    inference(pure_predicate_removal,[],[f6])).
% 2.22/1.00  
% 2.22/1.00  fof(f22,plain,(
% 2.22/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/1.00    inference(ennf_transformation,[],[f16])).
% 2.22/1.00  
% 2.22/1.00  fof(f47,plain,(
% 2.22/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/1.00    inference(cnf_transformation,[],[f22])).
% 2.22/1.00  
% 2.22/1.00  fof(f10,axiom,(
% 2.22/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f27,plain,(
% 2.22/1.00    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.22/1.00    inference(ennf_transformation,[],[f10])).
% 2.22/1.00  
% 2.22/1.00  fof(f28,plain,(
% 2.22/1.00    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.22/1.00    inference(flattening,[],[f27])).
% 2.22/1.00  
% 2.22/1.00  fof(f53,plain,(
% 2.22/1.00    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f28])).
% 2.22/1.00  
% 2.22/1.00  fof(f5,axiom,(
% 2.22/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f21,plain,(
% 2.22/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/1.00    inference(ennf_transformation,[],[f5])).
% 2.22/1.00  
% 2.22/1.00  fof(f46,plain,(
% 2.22/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/1.00    inference(cnf_transformation,[],[f21])).
% 2.22/1.00  
% 2.22/1.00  fof(f66,plain,(
% 2.22/1.00    v1_funct_1(sK4)),
% 2.22/1.00    inference(cnf_transformation,[],[f41])).
% 2.22/1.00  
% 2.22/1.00  fof(f11,axiom,(
% 2.22/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f29,plain,(
% 2.22/1.00    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.22/1.00    inference(ennf_transformation,[],[f11])).
% 2.22/1.00  
% 2.22/1.00  fof(f30,plain,(
% 2.22/1.00    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.22/1.00    inference(flattening,[],[f29])).
% 2.22/1.00  
% 2.22/1.00  fof(f54,plain,(
% 2.22/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f30])).
% 2.22/1.00  
% 2.22/1.00  fof(f71,plain,(
% 2.22/1.00    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5)),
% 2.22/1.00    inference(cnf_transformation,[],[f41])).
% 2.22/1.00  
% 2.22/1.00  fof(f7,axiom,(
% 2.22/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f23,plain,(
% 2.22/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.22/1.00    inference(ennf_transformation,[],[f7])).
% 2.22/1.00  
% 2.22/1.00  fof(f48,plain,(
% 2.22/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f23])).
% 2.22/1.00  
% 2.22/1.00  fof(f9,axiom,(
% 2.22/1.00    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f25,plain,(
% 2.22/1.00    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.22/1.00    inference(ennf_transformation,[],[f9])).
% 2.22/1.00  
% 2.22/1.00  fof(f26,plain,(
% 2.22/1.00    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.22/1.00    inference(flattening,[],[f25])).
% 2.22/1.00  
% 2.22/1.00  fof(f51,plain,(
% 2.22/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f26])).
% 2.22/1.00  
% 2.22/1.00  fof(f4,axiom,(
% 2.22/1.00    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f20,plain,(
% 2.22/1.00    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 2.22/1.00    inference(ennf_transformation,[],[f4])).
% 2.22/1.00  
% 2.22/1.00  fof(f45,plain,(
% 2.22/1.00    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f20])).
% 2.22/1.00  
% 2.22/1.00  cnf(c_23,negated_conjecture,
% 2.22/1.00      ( m1_subset_1(sK5,sK1) ),
% 2.22/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_638,negated_conjecture,
% 2.22/1.00      ( m1_subset_1(sK5,sK1) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1062,plain,
% 2.22/1.00      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_638]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_2,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.22/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_645,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0_51,X1_51)
% 2.22/1.00      | r2_hidden(X0_51,X1_51)
% 2.22/1.00      | v1_xboole_0(X1_51) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1057,plain,
% 2.22/1.00      ( m1_subset_1(X0_51,X1_51) != iProver_top
% 2.22/1.00      | r2_hidden(X0_51,X1_51) = iProver_top
% 2.22/1.00      | v1_xboole_0(X1_51) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1637,plain,
% 2.22/1.00      ( r2_hidden(sK5,sK1) = iProver_top
% 2.22/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 2.22/1.00      inference(superposition,[status(thm)],[c_1062,c_1057]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_36,plain,
% 2.22/1.00      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_21,negated_conjecture,
% 2.22/1.00      ( k1_xboole_0 != sK1 ),
% 2.22/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_639,negated_conjecture,
% 2.22/1.00      ( k1_xboole_0 != sK1 ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1,plain,
% 2.22/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.22/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_646,plain,
% 2.22/1.00      ( ~ v1_xboole_0(X0_51) | k1_xboole_0 = X0_51 ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1278,plain,
% 2.22/1.00      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_646]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1279,plain,
% 2.22/1.00      ( k1_xboole_0 = sK1 | v1_xboole_0(sK1) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_1278]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1353,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0_51,sK1)
% 2.22/1.00      | r2_hidden(X0_51,sK1)
% 2.22/1.00      | v1_xboole_0(sK1) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_645]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1520,plain,
% 2.22/1.00      ( ~ m1_subset_1(sK5,sK1) | r2_hidden(sK5,sK1) | v1_xboole_0(sK1) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_1353]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1521,plain,
% 2.22/1.00      ( m1_subset_1(sK5,sK1) != iProver_top
% 2.22/1.00      | r2_hidden(sK5,sK1) = iProver_top
% 2.22/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_1520]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1710,plain,
% 2.22/1.00      ( r2_hidden(sK5,sK1) = iProver_top ),
% 2.22/1.00      inference(global_propositional_subsumption,
% 2.22/1.00                [status(thm)],
% 2.22/1.00                [c_1637,c_36,c_639,c_1279,c_1521]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_15,plain,
% 2.22/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.22/1.00      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 2.22/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.22/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.22/1.00      | ~ v1_funct_1(X0)
% 2.22/1.00      | k1_xboole_0 = X2 ),
% 2.22/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_22,negated_conjecture,
% 2.22/1.00      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
% 2.22/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_431,plain,
% 2.22/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.22/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.22/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.22/1.00      | ~ v1_funct_1(X0)
% 2.22/1.00      | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
% 2.22/1.00      | k1_relset_1(sK2,sK0,sK4) != X3
% 2.22/1.00      | k1_xboole_0 = X2 ),
% 2.22/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_432,plain,
% 2.22/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.22/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.22/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_relset_1(sK2,sK0,sK4))))
% 2.22/1.00      | ~ v1_funct_1(X0)
% 2.22/1.00      | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
% 2.22/1.00      | k1_xboole_0 = X2 ),
% 2.22/1.00      inference(unflattening,[status(thm)],[c_431]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_625,plain,
% 2.22/1.00      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 2.22/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 2.22/1.00      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,k1_relset_1(sK2,sK0,sK4))))
% 2.22/1.00      | ~ v1_funct_1(X0_51)
% 2.22/1.00      | k2_relset_1(X1_51,X2_51,X0_51) != k2_relset_1(sK1,sK2,sK3)
% 2.22/1.00      | k1_xboole_0 = X2_51 ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_432]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1075,plain,
% 2.22/1.00      ( k2_relset_1(X0_51,X1_51,X2_51) != k2_relset_1(sK1,sK2,sK3)
% 2.22/1.00      | k1_xboole_0 = X1_51
% 2.22/1.00      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 2.22/1.00      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.22/1.00      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,k1_relset_1(sK2,sK0,sK4)))) = iProver_top
% 2.22/1.00      | v1_funct_1(X2_51) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_625]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1866,plain,
% 2.22/1.00      ( sK2 = k1_xboole_0
% 2.22/1.00      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.22/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relset_1(sK2,sK0,sK4)))) = iProver_top
% 2.22/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.22/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.22/1.00      inference(equality_resolution,[status(thm)],[c_1075]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_29,negated_conjecture,
% 2.22/1.00      ( ~ v1_xboole_0(sK2) ),
% 2.22/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_28,negated_conjecture,
% 2.22/1.00      ( v1_funct_1(sK3) ),
% 2.22/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_31,plain,
% 2.22/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_27,negated_conjecture,
% 2.22/1.00      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.22/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_32,plain,
% 2.22/1.00      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_26,negated_conjecture,
% 2.22/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.22/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_33,plain,
% 2.22/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_0,plain,
% 2.22/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.22/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_654,plain,
% 2.22/1.00      ( ~ v1_xboole_0(X0_51) | v1_xboole_0(X1_51) | X1_51 != X0_51 ),
% 2.22/1.00      theory(equality) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1285,plain,
% 2.22/1.00      ( ~ v1_xboole_0(X0_51) | v1_xboole_0(sK2) | sK2 != X0_51 ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_654]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1287,plain,
% 2.22/1.00      ( v1_xboole_0(sK2)
% 2.22/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 2.22/1.00      | sK2 != k1_xboole_0 ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_1285]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_2915,plain,
% 2.22/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relset_1(sK2,sK0,sK4)))) = iProver_top ),
% 2.22/1.00      inference(global_propositional_subsumption,
% 2.22/1.00                [status(thm)],
% 2.22/1.00                [c_1866,c_29,c_31,c_32,c_33,c_0,c_1287]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_24,negated_conjecture,
% 2.22/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 2.22/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_637,negated_conjecture,
% 2.22/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1063,plain,
% 2.22/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_637]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_7,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.22/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.22/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_642,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 2.22/1.00      | k1_relset_1(X1_51,X2_51,X0_51) = k1_relat_1(X0_51) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1060,plain,
% 2.22/1.00      ( k1_relset_1(X0_51,X1_51,X2_51) = k1_relat_1(X2_51)
% 2.22/1.00      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_2007,plain,
% 2.22/1.00      ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
% 2.22/1.00      inference(superposition,[status(thm)],[c_1063,c_1060]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_2919,plain,
% 2.22/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) = iProver_top ),
% 2.22/1.00      inference(light_normalisation,[status(thm)],[c_2915,c_2007]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_13,plain,
% 2.22/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.22/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.22/1.00      | ~ r2_hidden(X3,X1)
% 2.22/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.22/1.00      | ~ v1_funct_1(X0)
% 2.22/1.00      | k1_xboole_0 = X2 ),
% 2.22/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_641,plain,
% 2.22/1.00      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 2.22/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 2.22/1.00      | ~ r2_hidden(X3_51,X1_51)
% 2.22/1.00      | r2_hidden(k1_funct_1(X0_51,X3_51),X2_51)
% 2.22/1.00      | ~ v1_funct_1(X0_51)
% 2.22/1.00      | k1_xboole_0 = X2_51 ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1061,plain,
% 2.22/1.00      ( k1_xboole_0 = X0_51
% 2.22/1.00      | v1_funct_2(X1_51,X2_51,X0_51) != iProver_top
% 2.22/1.00      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X0_51))) != iProver_top
% 2.22/1.00      | r2_hidden(X3_51,X2_51) != iProver_top
% 2.22/1.00      | r2_hidden(k1_funct_1(X1_51,X3_51),X0_51) = iProver_top
% 2.22/1.00      | v1_funct_1(X1_51) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_2925,plain,
% 2.22/1.00      ( k1_relat_1(sK4) = k1_xboole_0
% 2.22/1.00      | v1_funct_2(sK3,sK1,k1_relat_1(sK4)) != iProver_top
% 2.22/1.00      | r2_hidden(X0_51,sK1) != iProver_top
% 2.22/1.00      | r2_hidden(k1_funct_1(sK3,X0_51),k1_relat_1(sK4)) = iProver_top
% 2.22/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.22/1.00      inference(superposition,[status(thm)],[c_2919,c_1061]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_17,plain,
% 2.22/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.22/1.00      | v1_funct_2(X0,X1,X3)
% 2.22/1.00      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 2.22/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.22/1.00      | ~ v1_funct_1(X0)
% 2.22/1.00      | k1_xboole_0 = X2 ),
% 2.22/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_408,plain,
% 2.22/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.22/1.00      | v1_funct_2(X0,X1,X3)
% 2.22/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.22/1.00      | ~ v1_funct_1(X0)
% 2.22/1.00      | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
% 2.22/1.00      | k1_relset_1(sK2,sK0,sK4) != X3
% 2.22/1.00      | k1_xboole_0 = X2 ),
% 2.22/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_409,plain,
% 2.22/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.22/1.00      | v1_funct_2(X0,X1,k1_relset_1(sK2,sK0,sK4))
% 2.22/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.22/1.00      | ~ v1_funct_1(X0)
% 2.22/1.00      | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
% 2.22/1.00      | k1_xboole_0 = X2 ),
% 2.22/1.00      inference(unflattening,[status(thm)],[c_408]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_626,plain,
% 2.22/1.00      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 2.22/1.00      | v1_funct_2(X0_51,X1_51,k1_relset_1(sK2,sK0,sK4))
% 2.22/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 2.22/1.00      | ~ v1_funct_1(X0_51)
% 2.22/1.00      | k2_relset_1(X1_51,X2_51,X0_51) != k2_relset_1(sK1,sK2,sK3)
% 2.22/1.00      | k1_xboole_0 = X2_51 ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_409]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1074,plain,
% 2.22/1.00      ( k2_relset_1(X0_51,X1_51,X2_51) != k2_relset_1(sK1,sK2,sK3)
% 2.22/1.00      | k1_xboole_0 = X1_51
% 2.22/1.00      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 2.22/1.00      | v1_funct_2(X2_51,X0_51,k1_relset_1(sK2,sK0,sK4)) = iProver_top
% 2.22/1.00      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.22/1.00      | v1_funct_1(X2_51) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1857,plain,
% 2.22/1.00      ( sK2 = k1_xboole_0
% 2.22/1.00      | v1_funct_2(sK3,sK1,k1_relset_1(sK2,sK0,sK4)) = iProver_top
% 2.22/1.00      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.22/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.22/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.22/1.00      inference(equality_resolution,[status(thm)],[c_1074]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_2569,plain,
% 2.22/1.00      ( v1_funct_2(sK3,sK1,k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
% 2.22/1.00      inference(global_propositional_subsumption,
% 2.22/1.00                [status(thm)],
% 2.22/1.00                [c_1857,c_29,c_31,c_32,c_33,c_0,c_1287]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_2573,plain,
% 2.22/1.00      ( v1_funct_2(sK3,sK1,k1_relat_1(sK4)) = iProver_top ),
% 2.22/1.00      inference(light_normalisation,[status(thm)],[c_2569,c_2007]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3612,plain,
% 2.22/1.00      ( r2_hidden(k1_funct_1(sK3,X0_51),k1_relat_1(sK4)) = iProver_top
% 2.22/1.00      | r2_hidden(X0_51,sK1) != iProver_top
% 2.22/1.00      | k1_relat_1(sK4) = k1_xboole_0 ),
% 2.22/1.00      inference(global_propositional_subsumption,
% 2.22/1.00                [status(thm)],
% 2.22/1.00                [c_2925,c_31,c_2573]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3613,plain,
% 2.22/1.00      ( k1_relat_1(sK4) = k1_xboole_0
% 2.22/1.00      | r2_hidden(X0_51,sK1) != iProver_top
% 2.22/1.00      | r2_hidden(k1_funct_1(sK3,X0_51),k1_relat_1(sK4)) = iProver_top ),
% 2.22/1.00      inference(renaming,[status(thm)],[c_3612]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_5,plain,
% 2.22/1.00      ( v5_relat_1(X0,X1)
% 2.22/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.22/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_11,plain,
% 2.22/1.00      ( ~ v5_relat_1(X0,X1)
% 2.22/1.00      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.22/1.00      | ~ v1_relat_1(X0)
% 2.22/1.00      | ~ v1_funct_1(X0)
% 2.22/1.00      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.22/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_302,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.22/1.00      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.22/1.00      | ~ v1_relat_1(X0)
% 2.22/1.00      | ~ v1_funct_1(X0)
% 2.22/1.00      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.22/1.00      inference(resolution,[status(thm)],[c_5,c_11]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.22/1.00      | v1_relat_1(X0) ),
% 2.22/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_306,plain,
% 2.22/1.00      ( ~ r2_hidden(X3,k1_relat_1(X0))
% 2.22/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.22/1.00      | ~ v1_funct_1(X0)
% 2.22/1.00      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.22/1.00      inference(global_propositional_subsumption,
% 2.22/1.00                [status(thm)],
% 2.22/1.00                [c_302,c_4]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_307,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.22/1.00      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.22/1.00      | ~ v1_funct_1(X0)
% 2.22/1.00      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.22/1.00      inference(renaming,[status(thm)],[c_306]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_630,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 2.22/1.00      | ~ r2_hidden(X3_51,k1_relat_1(X0_51))
% 2.22/1.00      | ~ v1_funct_1(X0_51)
% 2.22/1.00      | k7_partfun1(X2_51,X0_51,X3_51) = k1_funct_1(X0_51,X3_51) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_307]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1070,plain,
% 2.22/1.00      ( k7_partfun1(X0_51,X1_51,X2_51) = k1_funct_1(X1_51,X2_51)
% 2.22/1.00      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X3_51,X0_51))) != iProver_top
% 2.22/1.00      | r2_hidden(X2_51,k1_relat_1(X1_51)) != iProver_top
% 2.22/1.00      | v1_funct_1(X1_51) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3357,plain,
% 2.22/1.00      ( k7_partfun1(sK0,sK4,X0_51) = k1_funct_1(sK4,X0_51)
% 2.22/1.00      | r2_hidden(X0_51,k1_relat_1(sK4)) != iProver_top
% 2.22/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.22/1.00      inference(superposition,[status(thm)],[c_1063,c_1070]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_25,negated_conjecture,
% 2.22/1.00      ( v1_funct_1(sK4) ),
% 2.22/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_34,plain,
% 2.22/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3417,plain,
% 2.22/1.00      ( r2_hidden(X0_51,k1_relat_1(sK4)) != iProver_top
% 2.22/1.00      | k7_partfun1(sK0,sK4,X0_51) = k1_funct_1(sK4,X0_51) ),
% 2.22/1.00      inference(global_propositional_subsumption,
% 2.22/1.00                [status(thm)],
% 2.22/1.00                [c_3357,c_34]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3418,plain,
% 2.22/1.00      ( k7_partfun1(sK0,sK4,X0_51) = k1_funct_1(sK4,X0_51)
% 2.22/1.00      | r2_hidden(X0_51,k1_relat_1(sK4)) != iProver_top ),
% 2.22/1.00      inference(renaming,[status(thm)],[c_3417]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3621,plain,
% 2.22/1.00      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0_51)) = k1_funct_1(sK4,k1_funct_1(sK3,X0_51))
% 2.22/1.00      | k1_relat_1(sK4) = k1_xboole_0
% 2.22/1.00      | r2_hidden(X0_51,sK1) != iProver_top ),
% 2.22/1.00      inference(superposition,[status(thm)],[c_3613,c_3418]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3629,plain,
% 2.22/1.00      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 2.22/1.00      | k1_relat_1(sK4) = k1_xboole_0 ),
% 2.22/1.00      inference(superposition,[status(thm)],[c_1710,c_3621]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_12,plain,
% 2.22/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.22/1.00      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 2.22/1.00      | ~ m1_subset_1(X5,X1)
% 2.22/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.22/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.22/1.00      | ~ v1_funct_1(X4)
% 2.22/1.00      | ~ v1_funct_1(X0)
% 2.22/1.00      | v1_xboole_0(X2)
% 2.22/1.00      | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k1_funct_1(X4,k1_funct_1(X0,X5))
% 2.22/1.00      | k1_xboole_0 = X1 ),
% 2.22/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_330,plain,
% 2.22/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.22/1.00      | ~ m1_subset_1(X3,X1)
% 2.22/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.22/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 2.22/1.00      | ~ v1_funct_1(X0)
% 2.22/1.00      | ~ v1_funct_1(X4)
% 2.22/1.00      | v1_xboole_0(X2)
% 2.22/1.00      | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
% 2.22/1.00      | k1_relset_1(X2,X5,X4) != k1_relset_1(sK2,sK0,sK4)
% 2.22/1.00      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 2.22/1.00      | k1_xboole_0 = X1 ),
% 2.22/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_629,plain,
% 2.22/1.00      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 2.22/1.00      | ~ m1_subset_1(X3_51,X1_51)
% 2.22/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 2.22/1.00      | ~ m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X5_51)))
% 2.22/1.00      | ~ v1_funct_1(X0_51)
% 2.22/1.00      | ~ v1_funct_1(X4_51)
% 2.22/1.00      | v1_xboole_0(X2_51)
% 2.22/1.00      | k2_relset_1(X1_51,X2_51,X0_51) != k2_relset_1(sK1,sK2,sK3)
% 2.22/1.00      | k1_relset_1(X2_51,X5_51,X4_51) != k1_relset_1(sK2,sK0,sK4)
% 2.22/1.00      | k1_funct_1(k8_funct_2(X1_51,X2_51,X5_51,X0_51,X4_51),X3_51) = k1_funct_1(X4_51,k1_funct_1(X0_51,X3_51))
% 2.22/1.00      | k1_xboole_0 = X1_51 ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_330]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1071,plain,
% 2.22/1.00      ( k2_relset_1(X0_51,X1_51,X2_51) != k2_relset_1(sK1,sK2,sK3)
% 2.22/1.00      | k1_relset_1(X1_51,X3_51,X4_51) != k1_relset_1(sK2,sK0,sK4)
% 2.22/1.00      | k1_funct_1(k8_funct_2(X0_51,X1_51,X3_51,X2_51,X4_51),X5_51) = k1_funct_1(X4_51,k1_funct_1(X2_51,X5_51))
% 2.22/1.00      | k1_xboole_0 = X0_51
% 2.22/1.00      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 2.22/1.00      | m1_subset_1(X5_51,X0_51) != iProver_top
% 2.22/1.00      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.22/1.00      | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X3_51))) != iProver_top
% 2.22/1.00      | v1_funct_1(X2_51) != iProver_top
% 2.22/1.00      | v1_funct_1(X4_51) != iProver_top
% 2.22/1.00      | v1_xboole_0(X1_51) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1967,plain,
% 2.22/1.00      ( k1_relset_1(sK2,X0_51,X1_51) != k1_relset_1(sK2,sK0,sK4)
% 2.22/1.00      | k1_funct_1(k8_funct_2(sK1,sK2,X0_51,sK3,X1_51),X2_51) = k1_funct_1(X1_51,k1_funct_1(sK3,X2_51))
% 2.22/1.00      | sK1 = k1_xboole_0
% 2.22/1.00      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.22/1.00      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51))) != iProver_top
% 2.22/1.00      | m1_subset_1(X2_51,sK1) != iProver_top
% 2.22/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.22/1.00      | v1_funct_1(X1_51) != iProver_top
% 2.22/1.00      | v1_funct_1(sK3) != iProver_top
% 2.22/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 2.22/1.00      inference(equality_resolution,[status(thm)],[c_1071]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_30,plain,
% 2.22/1.00      ( v1_xboole_0(sK2) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_649,plain,( X0_51 = X0_51 ),theory(equality) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_679,plain,
% 2.22/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_649]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_652,plain,
% 2.22/1.00      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 2.22/1.00      theory(equality) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1300,plain,
% 2.22/1.00      ( sK1 != X0_51 | k1_xboole_0 != X0_51 | k1_xboole_0 = sK1 ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_652]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1301,plain,
% 2.22/1.00      ( sK1 != k1_xboole_0
% 2.22/1.00      | k1_xboole_0 = sK1
% 2.22/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_1300]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_2953,plain,
% 2.22/1.00      ( m1_subset_1(X2_51,sK1) != iProver_top
% 2.22/1.00      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51))) != iProver_top
% 2.22/1.00      | k1_funct_1(k8_funct_2(sK1,sK2,X0_51,sK3,X1_51),X2_51) = k1_funct_1(X1_51,k1_funct_1(sK3,X2_51))
% 2.22/1.00      | k1_relset_1(sK2,X0_51,X1_51) != k1_relset_1(sK2,sK0,sK4)
% 2.22/1.00      | v1_funct_1(X1_51) != iProver_top ),
% 2.22/1.00      inference(global_propositional_subsumption,
% 2.22/1.00                [status(thm)],
% 2.22/1.00                [c_1967,c_30,c_31,c_32,c_33,c_679,c_639,c_1301]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_2954,plain,
% 2.22/1.00      ( k1_relset_1(sK2,X0_51,X1_51) != k1_relset_1(sK2,sK0,sK4)
% 2.22/1.00      | k1_funct_1(k8_funct_2(sK1,sK2,X0_51,sK3,X1_51),X2_51) = k1_funct_1(X1_51,k1_funct_1(sK3,X2_51))
% 2.22/1.00      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51))) != iProver_top
% 2.22/1.00      | m1_subset_1(X2_51,sK1) != iProver_top
% 2.22/1.00      | v1_funct_1(X1_51) != iProver_top ),
% 2.22/1.00      inference(renaming,[status(thm)],[c_2953]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_2959,plain,
% 2.22/1.00      ( k1_relset_1(sK2,X0_51,X1_51) != k1_relat_1(sK4)
% 2.22/1.00      | k1_funct_1(k8_funct_2(sK1,sK2,X0_51,sK3,X1_51),X2_51) = k1_funct_1(X1_51,k1_funct_1(sK3,X2_51))
% 2.22/1.00      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51))) != iProver_top
% 2.22/1.00      | m1_subset_1(X2_51,sK1) != iProver_top
% 2.22/1.00      | v1_funct_1(X1_51) != iProver_top ),
% 2.22/1.00      inference(light_normalisation,[status(thm)],[c_2954,c_2007]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_2968,plain,
% 2.22/1.00      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0_51) = k1_funct_1(sK4,k1_funct_1(sK3,X0_51))
% 2.22/1.00      | m1_subset_1(X0_51,sK1) != iProver_top
% 2.22/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 2.22/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.22/1.00      inference(superposition,[status(thm)],[c_2007,c_2959]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_35,plain,
% 2.22/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3069,plain,
% 2.22/1.00      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0_51) = k1_funct_1(sK4,k1_funct_1(sK3,X0_51))
% 2.22/1.00      | m1_subset_1(X0_51,sK1) != iProver_top ),
% 2.22/1.00      inference(global_propositional_subsumption,
% 2.22/1.00                [status(thm)],
% 2.22/1.00                [c_2968,c_34,c_35]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3077,plain,
% 2.22/1.00      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.22/1.00      inference(superposition,[status(thm)],[c_1062,c_3069]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_20,negated_conjecture,
% 2.22/1.00      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
% 2.22/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_640,negated_conjecture,
% 2.22/1.00      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3079,plain,
% 2.22/1.00      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.22/1.00      inference(demodulation,[status(thm)],[c_3077,c_640]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3680,plain,
% 2.22/1.00      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 2.22/1.00      inference(global_propositional_subsumption,
% 2.22/1.00                [status(thm)],
% 2.22/1.00                [c_3629,c_3079]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_6,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.22/1.00      | ~ v1_xboole_0(X2)
% 2.22/1.00      | v1_xboole_0(X0) ),
% 2.22/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_643,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 2.22/1.00      | ~ v1_xboole_0(X2_51)
% 2.22/1.00      | v1_xboole_0(X0_51) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1059,plain,
% 2.22/1.00      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 2.22/1.00      | v1_xboole_0(X2_51) != iProver_top
% 2.22/1.00      | v1_xboole_0(X0_51) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_643]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_2923,plain,
% 2.22/1.00      ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top
% 2.22/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 2.22/1.00      inference(superposition,[status(thm)],[c_2919,c_1059]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_9,plain,
% 2.22/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.22/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.22/1.00      | ~ v1_funct_1(X0)
% 2.22/1.00      | ~ v1_xboole_0(X0)
% 2.22/1.00      | v1_xboole_0(X1)
% 2.22/1.00      | v1_xboole_0(X2) ),
% 2.22/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3,plain,
% 2.22/1.00      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 2.22/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_148,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.22/1.00      | ~ v1_funct_2(X0,X1,X2)
% 2.22/1.00      | ~ v1_xboole_0(X0)
% 2.22/1.00      | v1_xboole_0(X1)
% 2.22/1.00      | v1_xboole_0(X2) ),
% 2.22/1.00      inference(global_propositional_subsumption,[status(thm)],[c_9,c_3]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_149,plain,
% 2.22/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.22/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.22/1.00      | ~ v1_xboole_0(X0)
% 2.22/1.00      | v1_xboole_0(X1)
% 2.22/1.00      | v1_xboole_0(X2) ),
% 2.22/1.00      inference(renaming,[status(thm)],[c_148]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_631,plain,
% 2.22/1.00      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 2.22/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 2.22/1.00      | ~ v1_xboole_0(X0_51)
% 2.22/1.00      | v1_xboole_0(X2_51)
% 2.22/1.00      | v1_xboole_0(X1_51) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_149]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1327,plain,
% 2.22/1.00      ( ~ v1_funct_2(X0_51,X1_51,sK2)
% 2.22/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK2)))
% 2.22/1.00      | ~ v1_xboole_0(X0_51)
% 2.22/1.00      | v1_xboole_0(X1_51)
% 2.22/1.00      | v1_xboole_0(sK2) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_631]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1462,plain,
% 2.22/1.00      ( ~ v1_funct_2(X0_51,sK1,sK2)
% 2.22/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.22/1.00      | ~ v1_xboole_0(X0_51)
% 2.22/1.00      | v1_xboole_0(sK2)
% 2.22/1.00      | v1_xboole_0(sK1) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_1327]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1832,plain,
% 2.22/1.00      ( ~ v1_funct_2(sK3,sK1,sK2)
% 2.22/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.22/1.00      | v1_xboole_0(sK2)
% 2.22/1.00      | v1_xboole_0(sK1)
% 2.22/1.00      | ~ v1_xboole_0(sK3) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_1462]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1833,plain,
% 2.22/1.00      ( v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.22/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.22/1.00      | v1_xboole_0(sK2) = iProver_top
% 2.22/1.00      | v1_xboole_0(sK1) = iProver_top
% 2.22/1.00      | v1_xboole_0(sK3) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_1832]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3324,plain,
% 2.22/1.00      ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top ),
% 2.22/1.00      inference(global_propositional_subsumption,
% 2.22/1.00                [status(thm)],
% 2.22/1.00                [c_2923,c_30,c_32,c_33,c_639,c_1279,c_1833]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3686,plain,
% 2.22/1.00      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.22/1.00      inference(demodulation,[status(thm)],[c_3680,c_3324]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_75,plain,
% 2.22/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(contradiction,plain,
% 2.22/1.00      ( $false ),
% 2.22/1.00      inference(minisat,[status(thm)],[c_3686,c_75]) ).
% 2.22/1.00  
% 2.22/1.00  
% 2.22/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.22/1.00  
% 2.22/1.00  ------                               Statistics
% 2.22/1.00  
% 2.22/1.00  ------ General
% 2.22/1.00  
% 2.22/1.00  abstr_ref_over_cycles:                  0
% 2.22/1.00  abstr_ref_under_cycles:                 0
% 2.22/1.00  gc_basic_clause_elim:                   0
% 2.22/1.00  forced_gc_time:                         0
% 2.22/1.00  parsing_time:                           0.009
% 2.22/1.00  unif_index_cands_time:                  0.
% 2.22/1.00  unif_index_add_time:                    0.
% 2.22/1.00  orderings_time:                         0.
% 2.22/1.00  out_proof_time:                         0.011
% 2.22/1.00  total_time:                             0.186
% 2.22/1.00  num_of_symbols:                         57
% 2.22/1.00  num_of_terms:                           5728
% 2.22/1.00  
% 2.22/1.00  ------ Preprocessing
% 2.22/1.00  
% 2.22/1.00  num_of_splits:                          0
% 2.22/1.00  num_of_split_atoms:                     0
% 2.22/1.00  num_of_reused_defs:                     0
% 2.22/1.00  num_eq_ax_congr_red:                    6
% 2.22/1.00  num_of_sem_filtered_clauses:            1
% 2.22/1.00  num_of_subtypes:                        3
% 2.22/1.00  monotx_restored_types:                  1
% 2.22/1.00  sat_num_of_epr_types:                   0
% 2.22/1.00  sat_num_of_non_cyclic_types:            0
% 2.22/1.00  sat_guarded_non_collapsed_types:        1
% 2.22/1.00  num_pure_diseq_elim:                    0
% 2.22/1.00  simp_replaced_by:                       0
% 2.22/1.00  res_preprocessed:                       130
% 2.22/1.00  prep_upred:                             0
% 2.22/1.00  prep_unflattend:                        4
% 2.22/1.00  smt_new_axioms:                         0
% 2.22/1.00  pred_elim_cands:                        5
% 2.22/1.00  pred_elim:                              3
% 2.22/1.00  pred_elim_cl:                           3
% 2.22/1.00  pred_elim_cycles:                       6
% 2.22/1.00  merged_defs:                            0
% 2.22/1.00  merged_defs_ncl:                        0
% 2.22/1.00  bin_hyper_res:                          0
% 2.22/1.00  prep_cycles:                            4
% 2.22/1.00  pred_elim_time:                         0.005
% 2.22/1.00  splitting_time:                         0.
% 2.22/1.00  sem_filter_time:                        0.
% 2.22/1.00  monotx_time:                            0.013
% 2.22/1.00  subtype_inf_time:                       0.014
% 2.22/1.00  
% 2.22/1.00  ------ Problem properties
% 2.22/1.00  
% 2.22/1.00  clauses:                                23
% 2.22/1.00  conjectures:                            9
% 2.22/1.00  epr:                                    10
% 2.22/1.00  horn:                                   17
% 2.22/1.00  ground:                                 10
% 2.22/1.00  unary:                                  10
% 2.22/1.00  binary:                                 3
% 2.22/1.00  lits:                                   70
% 2.22/1.00  lits_eq:                                16
% 2.22/1.00  fd_pure:                                0
% 2.22/1.00  fd_pseudo:                              0
% 2.22/1.00  fd_cond:                                5
% 2.22/1.00  fd_pseudo_cond:                         0
% 2.22/1.00  ac_symbols:                             0
% 2.22/1.00  
% 2.22/1.00  ------ Propositional Solver
% 2.22/1.00  
% 2.22/1.00  prop_solver_calls:                      28
% 2.22/1.00  prop_fast_solver_calls:                 1056
% 2.22/1.00  smt_solver_calls:                       0
% 2.22/1.00  smt_fast_solver_calls:                  0
% 2.22/1.00  prop_num_of_clauses:                    1353
% 2.22/1.00  prop_preprocess_simplified:             4879
% 2.22/1.00  prop_fo_subsumed:                       32
% 2.22/1.00  prop_solver_time:                       0.
% 2.22/1.00  smt_solver_time:                        0.
% 2.22/1.00  smt_fast_solver_time:                   0.
% 2.22/1.00  prop_fast_solver_time:                  0.
% 2.22/1.00  prop_unsat_core_time:                   0.
% 2.22/1.00  
% 2.22/1.00  ------ QBF
% 2.22/1.00  
% 2.22/1.00  qbf_q_res:                              0
% 2.22/1.00  qbf_num_tautologies:                    0
% 2.22/1.00  qbf_prep_cycles:                        0
% 2.22/1.00  
% 2.22/1.00  ------ BMC1
% 2.22/1.00  
% 2.22/1.00  bmc1_current_bound:                     -1
% 2.22/1.00  bmc1_last_solved_bound:                 -1
% 2.22/1.00  bmc1_unsat_core_size:                   -1
% 2.22/1.00  bmc1_unsat_core_parents_size:           -1
% 2.22/1.00  bmc1_merge_next_fun:                    0
% 2.22/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.22/1.00  
% 2.22/1.00  ------ Instantiation
% 2.22/1.00  
% 2.22/1.00  inst_num_of_clauses:                    377
% 2.22/1.00  inst_num_in_passive:                    92
% 2.22/1.00  inst_num_in_active:                     267
% 2.22/1.00  inst_num_in_unprocessed:                18
% 2.22/1.00  inst_num_of_loops:                      270
% 2.22/1.00  inst_num_of_learning_restarts:          0
% 2.22/1.00  inst_num_moves_active_passive:          0
% 2.22/1.00  inst_lit_activity:                      0
% 2.22/1.00  inst_lit_activity_moves:                0
% 2.22/1.00  inst_num_tautologies:                   0
% 2.22/1.00  inst_num_prop_implied:                  0
% 2.22/1.00  inst_num_existing_simplified:           0
% 2.22/1.00  inst_num_eq_res_simplified:             0
% 2.22/1.00  inst_num_child_elim:                    0
% 2.22/1.00  inst_num_of_dismatching_blockings:      12
% 2.22/1.00  inst_num_of_non_proper_insts:           275
% 2.22/1.00  inst_num_of_duplicates:                 0
% 2.22/1.00  inst_inst_num_from_inst_to_res:         0
% 2.22/1.00  inst_dismatching_checking_time:         0.
% 2.22/1.00  
% 2.22/1.00  ------ Resolution
% 2.22/1.00  
% 2.22/1.00  res_num_of_clauses:                     0
% 2.22/1.00  res_num_in_passive:                     0
% 2.22/1.00  res_num_in_active:                      0
% 2.22/1.00  res_num_of_loops:                       134
% 2.22/1.00  res_forward_subset_subsumed:            54
% 2.22/1.00  res_backward_subset_subsumed:           0
% 2.22/1.00  res_forward_subsumed:                   0
% 2.22/1.00  res_backward_subsumed:                  0
% 2.22/1.00  res_forward_subsumption_resolution:     0
% 2.22/1.00  res_backward_subsumption_resolution:    0
% 2.22/1.00  res_clause_to_clause_subsumption:       103
% 2.22/1.00  res_orphan_elimination:                 0
% 2.22/1.00  res_tautology_del:                      37
% 2.22/1.00  res_num_eq_res_simplified:              0
% 2.22/1.00  res_num_sel_changes:                    0
% 2.22/1.00  res_moves_from_active_to_pass:          0
% 2.22/1.00  
% 2.22/1.00  ------ Superposition
% 2.22/1.00  
% 2.22/1.00  sup_time_total:                         0.
% 2.22/1.00  sup_time_generating:                    0.
% 2.22/1.00  sup_time_sim_full:                      0.
% 2.22/1.00  sup_time_sim_immed:                     0.
% 2.22/1.00  
% 2.22/1.00  sup_num_of_clauses:                     38
% 2.22/1.00  sup_num_in_active:                      31
% 2.22/1.00  sup_num_in_passive:                     7
% 2.22/1.00  sup_num_of_loops:                       52
% 2.22/1.00  sup_fw_superposition:                   19
% 2.22/1.00  sup_bw_superposition:                   6
% 2.22/1.00  sup_immediate_simplified:               4
% 2.22/1.00  sup_given_eliminated:                   0
% 2.22/1.00  comparisons_done:                       0
% 2.22/1.00  comparisons_avoided:                    3
% 2.22/1.00  
% 2.22/1.00  ------ Simplifications
% 2.22/1.00  
% 2.22/1.00  
% 2.22/1.00  sim_fw_subset_subsumed:                 3
% 2.22/1.00  sim_bw_subset_subsumed:                 1
% 2.22/1.00  sim_fw_subsumed:                        1
% 2.22/1.00  sim_bw_subsumed:                        0
% 2.22/1.00  sim_fw_subsumption_res:                 0
% 2.22/1.00  sim_bw_subsumption_res:                 0
% 2.22/1.00  sim_tautology_del:                      0
% 2.22/1.00  sim_eq_tautology_del:                   2
% 2.22/1.00  sim_eq_res_simp:                        0
% 2.22/1.00  sim_fw_demodulated:                     0
% 2.22/1.00  sim_bw_demodulated:                     20
% 2.22/1.00  sim_light_normalised:                   3
% 2.22/1.00  sim_joinable_taut:                      0
% 2.22/1.00  sim_joinable_simp:                      0
% 2.22/1.00  sim_ac_normalised:                      0
% 2.22/1.00  sim_smt_subsumption:                    0
% 2.22/1.00  
%------------------------------------------------------------------------------

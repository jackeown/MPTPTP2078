%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:46 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 640 expanded)
%              Number of clauses        :   97 ( 171 expanded)
%              Number of leaves         :   20 ( 222 expanded)
%              Depth                    :   20
%              Number of atoms          :  642 (5006 expanded)
%              Number of equality atoms :  263 (1348 expanded)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f36,f42,f41,f40,f39])).

fof(f71,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

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

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

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

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
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

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f56,plain,(
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

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

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

fof(f57,plain,(
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

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f74,plain,(
    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1057,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1062,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2821,plain,
    ( r2_hidden(sK5,sK1) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1057,c_1062])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1287,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1288,plain,
    ( k1_xboole_0 = sK1
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1287])).

cnf(c_1375,plain,
    ( ~ m1_subset_1(X0,sK1)
    | r2_hidden(X0,sK1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1669,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | r2_hidden(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_1670,plain,
    ( m1_subset_1(sK5,sK1) != iProver_top
    | r2_hidden(sK5,sK1) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1669])).

cnf(c_2910,plain,
    ( r2_hidden(sK5,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2821,c_37,c_22,c_1288,c_1670])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1056,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1061,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2066,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1056,c_1061])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_449,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
    | k1_relset_1(sK2,sK0,sK4) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_450,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_relset_1(sK2,sK0,sK4))))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_1045,plain,
    ( k2_relset_1(X0,X1,X2) != k2_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relset_1(sK2,sK0,sK4)))) = iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_1448,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relset_1(sK2,sK0,sK4)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1045])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_32,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_33,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_670,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1295,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_1297,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_1807,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relset_1(sK2,sK0,sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1448,c_30,c_32,c_33,c_34,c_0,c_1297])).

cnf(c_2220,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2066,c_1807])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1058,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3185,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(sK3,sK1,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2220,c_1058])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_426,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
    | k1_relset_1(sK2,sK0,sK4) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_427,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,k1_relset_1(sK2,sK0,sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_1046,plain,
    ( k2_relset_1(X0,X1,X2) != k2_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X2,X0,k1_relset_1(sK2,sK0,sK4)) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_1710,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,k1_relset_1(sK2,sK0,sK4)) = iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1046])).

cnf(c_1779,plain,
    ( v1_funct_2(sK3,sK1,k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1710,c_30,c_32,c_33,c_34,c_0,c_1297])).

cnf(c_2221,plain,
    ( v1_funct_2(sK3,sK1,k1_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2066,c_1779])).

cnf(c_4264,plain,
    ( r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,sK1) != iProver_top
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3185,c_32,c_2221])).

cnf(c_4265,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4264])).

cnf(c_7,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_289,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_7,c_12])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_293,plain,
    ( ~ v1_funct_1(X0)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_289,c_6])).

cnf(c_294,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(renaming,[status(thm)],[c_293])).

cnf(c_1050,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_1895,plain,
    ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1050])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_35,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2551,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1895,c_35])).

cnf(c_2552,plain,
    ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2551])).

cnf(c_4274,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | k1_relat_1(sK4) = k1_xboole_0
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4265,c_2552])).

cnf(c_4510,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2910,c_4274])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f57])).

cnf(c_348,plain,
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
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_1049,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_1724,plain,
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
    inference(equality_resolution,[status(thm)],[c_1049])).

cnf(c_31,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_71,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_72,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_669,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1317,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_1318,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1317])).

cnf(c_1813,plain,
    ( m1_subset_1(X2,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1724,c_31,c_32,c_33,c_34,c_22,c_71,c_72,c_1318])).

cnf(c_1814,plain,
    ( k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1813])).

cnf(c_1824,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1814])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1881,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1824,c_35,c_36])).

cnf(c_1889,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1057,c_1881])).

cnf(c_21,negated_conjecture,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2407,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_1889,c_21])).

cnf(c_4533,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4510,c_2407])).

cnf(c_9,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1060,plain,
    ( v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3184,plain,
    ( v1_partfun1(sK3,sK1) != iProver_top
    | v1_xboole_0(k1_relat_1(sK4)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2220,c_1060])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1347,plain,
    ( ~ v1_funct_2(X0,X1,sK2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1544,plain,
    ( ~ v1_funct_2(sK3,X0,sK2)
    | v1_partfun1(sK3,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1347])).

cnf(c_1769,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | v1_partfun1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1544])).

cnf(c_1770,plain,
    ( v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_partfun1(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1769])).

cnf(c_4253,plain,
    ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3184,c_31,c_32,c_33,c_34,c_22,c_1288,c_1770])).

cnf(c_4537,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4533,c_4253])).

cnf(c_76,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4537,c_76])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:02:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.51/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/0.98  
% 2.51/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.51/0.98  
% 2.51/0.98  ------  iProver source info
% 2.51/0.98  
% 2.51/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.51/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.51/0.98  git: non_committed_changes: false
% 2.51/0.98  git: last_make_outside_of_git: false
% 2.51/0.98  
% 2.51/0.98  ------ 
% 2.51/0.98  
% 2.51/0.98  ------ Input Options
% 2.51/0.98  
% 2.51/0.98  --out_options                           all
% 2.51/0.98  --tptp_safe_out                         true
% 2.51/0.98  --problem_path                          ""
% 2.51/0.98  --include_path                          ""
% 2.51/0.98  --clausifier                            res/vclausify_rel
% 2.51/0.98  --clausifier_options                    --mode clausify
% 2.51/0.98  --stdin                                 false
% 2.51/0.98  --stats_out                             all
% 2.51/0.98  
% 2.51/0.98  ------ General Options
% 2.51/0.98  
% 2.51/0.98  --fof                                   false
% 2.51/0.98  --time_out_real                         305.
% 2.51/0.98  --time_out_virtual                      -1.
% 2.51/0.98  --symbol_type_check                     false
% 2.51/0.98  --clausify_out                          false
% 2.51/0.98  --sig_cnt_out                           false
% 2.51/0.98  --trig_cnt_out                          false
% 2.51/0.98  --trig_cnt_out_tolerance                1.
% 2.51/0.98  --trig_cnt_out_sk_spl                   false
% 2.51/0.98  --abstr_cl_out                          false
% 2.51/0.98  
% 2.51/0.98  ------ Global Options
% 2.51/0.98  
% 2.51/0.98  --schedule                              default
% 2.51/0.98  --add_important_lit                     false
% 2.51/0.98  --prop_solver_per_cl                    1000
% 2.51/0.98  --min_unsat_core                        false
% 2.51/0.98  --soft_assumptions                      false
% 2.51/0.98  --soft_lemma_size                       3
% 2.51/0.98  --prop_impl_unit_size                   0
% 2.51/0.98  --prop_impl_unit                        []
% 2.51/0.98  --share_sel_clauses                     true
% 2.51/0.98  --reset_solvers                         false
% 2.51/0.98  --bc_imp_inh                            [conj_cone]
% 2.51/0.98  --conj_cone_tolerance                   3.
% 2.51/0.98  --extra_neg_conj                        none
% 2.51/0.98  --large_theory_mode                     true
% 2.51/0.98  --prolific_symb_bound                   200
% 2.51/0.98  --lt_threshold                          2000
% 2.51/0.98  --clause_weak_htbl                      true
% 2.51/0.98  --gc_record_bc_elim                     false
% 2.51/0.98  
% 2.51/0.98  ------ Preprocessing Options
% 2.51/0.98  
% 2.51/0.98  --preprocessing_flag                    true
% 2.51/0.98  --time_out_prep_mult                    0.1
% 2.51/0.98  --splitting_mode                        input
% 2.51/0.98  --splitting_grd                         true
% 2.51/0.98  --splitting_cvd                         false
% 2.51/0.98  --splitting_cvd_svl                     false
% 2.51/0.98  --splitting_nvd                         32
% 2.51/0.98  --sub_typing                            true
% 2.51/0.98  --prep_gs_sim                           true
% 2.51/0.98  --prep_unflatten                        true
% 2.51/0.98  --prep_res_sim                          true
% 2.51/0.98  --prep_upred                            true
% 2.51/0.98  --prep_sem_filter                       exhaustive
% 2.51/0.98  --prep_sem_filter_out                   false
% 2.51/0.98  --pred_elim                             true
% 2.51/0.98  --res_sim_input                         true
% 2.51/0.98  --eq_ax_congr_red                       true
% 2.51/0.98  --pure_diseq_elim                       true
% 2.51/0.98  --brand_transform                       false
% 2.51/0.98  --non_eq_to_eq                          false
% 2.51/0.98  --prep_def_merge                        true
% 2.51/0.98  --prep_def_merge_prop_impl              false
% 2.51/0.98  --prep_def_merge_mbd                    true
% 2.51/0.98  --prep_def_merge_tr_red                 false
% 2.51/0.98  --prep_def_merge_tr_cl                  false
% 2.51/0.98  --smt_preprocessing                     true
% 2.51/0.98  --smt_ac_axioms                         fast
% 2.51/0.98  --preprocessed_out                      false
% 2.51/0.98  --preprocessed_stats                    false
% 2.51/0.98  
% 2.51/0.98  ------ Abstraction refinement Options
% 2.51/0.98  
% 2.51/0.98  --abstr_ref                             []
% 2.51/0.98  --abstr_ref_prep                        false
% 2.51/0.98  --abstr_ref_until_sat                   false
% 2.51/0.98  --abstr_ref_sig_restrict                funpre
% 2.51/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.51/0.98  --abstr_ref_under                       []
% 2.51/0.98  
% 2.51/0.98  ------ SAT Options
% 2.51/0.98  
% 2.51/0.98  --sat_mode                              false
% 2.51/0.98  --sat_fm_restart_options                ""
% 2.51/0.98  --sat_gr_def                            false
% 2.51/0.98  --sat_epr_types                         true
% 2.51/0.98  --sat_non_cyclic_types                  false
% 2.51/0.98  --sat_finite_models                     false
% 2.51/0.98  --sat_fm_lemmas                         false
% 2.51/0.98  --sat_fm_prep                           false
% 2.51/0.98  --sat_fm_uc_incr                        true
% 2.51/0.98  --sat_out_model                         small
% 2.51/0.98  --sat_out_clauses                       false
% 2.51/0.98  
% 2.51/0.98  ------ QBF Options
% 2.51/0.98  
% 2.51/0.98  --qbf_mode                              false
% 2.51/0.98  --qbf_elim_univ                         false
% 2.51/0.98  --qbf_dom_inst                          none
% 2.51/0.98  --qbf_dom_pre_inst                      false
% 2.51/0.98  --qbf_sk_in                             false
% 2.51/0.98  --qbf_pred_elim                         true
% 2.51/0.98  --qbf_split                             512
% 2.51/0.98  
% 2.51/0.98  ------ BMC1 Options
% 2.51/0.98  
% 2.51/0.98  --bmc1_incremental                      false
% 2.51/0.98  --bmc1_axioms                           reachable_all
% 2.51/0.98  --bmc1_min_bound                        0
% 2.51/0.98  --bmc1_max_bound                        -1
% 2.51/0.98  --bmc1_max_bound_default                -1
% 2.51/0.98  --bmc1_symbol_reachability              true
% 2.51/0.98  --bmc1_property_lemmas                  false
% 2.51/0.98  --bmc1_k_induction                      false
% 2.51/0.98  --bmc1_non_equiv_states                 false
% 2.51/0.98  --bmc1_deadlock                         false
% 2.51/0.98  --bmc1_ucm                              false
% 2.51/0.98  --bmc1_add_unsat_core                   none
% 2.51/0.98  --bmc1_unsat_core_children              false
% 2.51/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.51/0.98  --bmc1_out_stat                         full
% 2.51/0.98  --bmc1_ground_init                      false
% 2.51/0.98  --bmc1_pre_inst_next_state              false
% 2.51/0.98  --bmc1_pre_inst_state                   false
% 2.51/0.98  --bmc1_pre_inst_reach_state             false
% 2.51/0.98  --bmc1_out_unsat_core                   false
% 2.51/0.98  --bmc1_aig_witness_out                  false
% 2.51/0.98  --bmc1_verbose                          false
% 2.51/0.98  --bmc1_dump_clauses_tptp                false
% 2.51/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.51/0.98  --bmc1_dump_file                        -
% 2.51/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.51/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.51/0.98  --bmc1_ucm_extend_mode                  1
% 2.51/0.98  --bmc1_ucm_init_mode                    2
% 2.51/0.98  --bmc1_ucm_cone_mode                    none
% 2.51/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.51/0.98  --bmc1_ucm_relax_model                  4
% 2.51/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.51/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.51/0.98  --bmc1_ucm_layered_model                none
% 2.51/0.98  --bmc1_ucm_max_lemma_size               10
% 2.51/0.98  
% 2.51/0.98  ------ AIG Options
% 2.51/0.98  
% 2.51/0.98  --aig_mode                              false
% 2.51/0.98  
% 2.51/0.98  ------ Instantiation Options
% 2.51/0.98  
% 2.51/0.98  --instantiation_flag                    true
% 2.51/0.98  --inst_sos_flag                         false
% 2.51/0.98  --inst_sos_phase                        true
% 2.51/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.51/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.51/0.98  --inst_lit_sel_side                     num_symb
% 2.51/0.98  --inst_solver_per_active                1400
% 2.51/0.98  --inst_solver_calls_frac                1.
% 2.51/0.98  --inst_passive_queue_type               priority_queues
% 2.51/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.51/0.98  --inst_passive_queues_freq              [25;2]
% 2.51/0.98  --inst_dismatching                      true
% 2.51/0.98  --inst_eager_unprocessed_to_passive     true
% 2.51/0.98  --inst_prop_sim_given                   true
% 2.51/0.98  --inst_prop_sim_new                     false
% 2.51/0.98  --inst_subs_new                         false
% 2.51/0.98  --inst_eq_res_simp                      false
% 2.51/0.98  --inst_subs_given                       false
% 2.51/0.98  --inst_orphan_elimination               true
% 2.51/0.98  --inst_learning_loop_flag               true
% 2.51/0.98  --inst_learning_start                   3000
% 2.51/0.98  --inst_learning_factor                  2
% 2.51/0.98  --inst_start_prop_sim_after_learn       3
% 2.51/0.98  --inst_sel_renew                        solver
% 2.51/0.98  --inst_lit_activity_flag                true
% 2.51/0.98  --inst_restr_to_given                   false
% 2.51/0.98  --inst_activity_threshold               500
% 2.51/0.98  --inst_out_proof                        true
% 2.51/0.98  
% 2.51/0.98  ------ Resolution Options
% 2.51/0.98  
% 2.51/0.98  --resolution_flag                       true
% 2.51/0.98  --res_lit_sel                           adaptive
% 2.51/0.98  --res_lit_sel_side                      none
% 2.51/0.98  --res_ordering                          kbo
% 2.51/0.98  --res_to_prop_solver                    active
% 2.51/0.98  --res_prop_simpl_new                    false
% 2.51/0.98  --res_prop_simpl_given                  true
% 2.51/0.98  --res_passive_queue_type                priority_queues
% 2.51/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.51/0.98  --res_passive_queues_freq               [15;5]
% 2.51/0.98  --res_forward_subs                      full
% 2.51/0.98  --res_backward_subs                     full
% 2.51/0.98  --res_forward_subs_resolution           true
% 2.51/0.98  --res_backward_subs_resolution          true
% 2.51/0.98  --res_orphan_elimination                true
% 2.51/0.98  --res_time_limit                        2.
% 2.51/0.98  --res_out_proof                         true
% 2.51/0.98  
% 2.51/0.98  ------ Superposition Options
% 2.51/0.98  
% 2.51/0.98  --superposition_flag                    true
% 2.51/0.98  --sup_passive_queue_type                priority_queues
% 2.51/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.51/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.51/0.98  --demod_completeness_check              fast
% 2.51/0.98  --demod_use_ground                      true
% 2.51/0.98  --sup_to_prop_solver                    passive
% 2.51/0.98  --sup_prop_simpl_new                    true
% 2.51/0.98  --sup_prop_simpl_given                  true
% 2.51/0.98  --sup_fun_splitting                     false
% 2.51/0.98  --sup_smt_interval                      50000
% 2.51/0.98  
% 2.51/0.98  ------ Superposition Simplification Setup
% 2.51/0.98  
% 2.51/0.98  --sup_indices_passive                   []
% 2.51/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.51/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.98  --sup_full_bw                           [BwDemod]
% 2.51/0.98  --sup_immed_triv                        [TrivRules]
% 2.51/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.51/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.98  --sup_immed_bw_main                     []
% 2.51/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.51/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/0.98  
% 2.51/0.98  ------ Combination Options
% 2.51/0.98  
% 2.51/0.98  --comb_res_mult                         3
% 2.51/0.98  --comb_sup_mult                         2
% 2.51/0.98  --comb_inst_mult                        10
% 2.51/0.98  
% 2.51/0.98  ------ Debug Options
% 2.51/0.98  
% 2.51/0.98  --dbg_backtrace                         false
% 2.51/0.98  --dbg_dump_prop_clauses                 false
% 2.51/0.98  --dbg_dump_prop_clauses_file            -
% 2.51/0.98  --dbg_out_stat                          false
% 2.51/0.98  ------ Parsing...
% 2.51/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.51/0.98  
% 2.51/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.51/0.98  
% 2.51/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.51/0.98  
% 2.51/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.51/0.98  ------ Proving...
% 2.51/0.98  ------ Problem Properties 
% 2.51/0.98  
% 2.51/0.98  
% 2.51/0.98  clauses                                 25
% 2.51/0.98  conjectures                             9
% 2.51/0.98  EPR                                     9
% 2.51/0.98  Horn                                    18
% 2.51/0.98  unary                                   12
% 2.51/0.98  binary                                  2
% 2.51/0.98  lits                                    74
% 2.51/0.98  lits eq                                 21
% 2.51/0.98  fd_pure                                 0
% 2.51/0.98  fd_pseudo                               0
% 2.51/0.98  fd_cond                                 6
% 2.51/0.98  fd_pseudo_cond                          0
% 2.51/0.98  AC symbols                              0
% 2.51/0.98  
% 2.51/0.98  ------ Schedule dynamic 5 is on 
% 2.51/0.98  
% 2.51/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.51/0.98  
% 2.51/0.98  
% 2.51/0.98  ------ 
% 2.51/0.98  Current options:
% 2.51/0.98  ------ 
% 2.51/0.98  
% 2.51/0.98  ------ Input Options
% 2.51/0.98  
% 2.51/0.98  --out_options                           all
% 2.51/0.98  --tptp_safe_out                         true
% 2.51/0.98  --problem_path                          ""
% 2.51/0.98  --include_path                          ""
% 2.51/0.98  --clausifier                            res/vclausify_rel
% 2.51/0.98  --clausifier_options                    --mode clausify
% 2.51/0.98  --stdin                                 false
% 2.51/0.98  --stats_out                             all
% 2.51/0.98  
% 2.51/0.98  ------ General Options
% 2.51/0.98  
% 2.51/0.98  --fof                                   false
% 2.51/0.98  --time_out_real                         305.
% 2.51/0.98  --time_out_virtual                      -1.
% 2.51/0.98  --symbol_type_check                     false
% 2.51/0.98  --clausify_out                          false
% 2.51/0.98  --sig_cnt_out                           false
% 2.51/0.98  --trig_cnt_out                          false
% 2.51/0.98  --trig_cnt_out_tolerance                1.
% 2.51/0.98  --trig_cnt_out_sk_spl                   false
% 2.51/0.98  --abstr_cl_out                          false
% 2.51/0.98  
% 2.51/0.98  ------ Global Options
% 2.51/0.98  
% 2.51/0.98  --schedule                              default
% 2.51/0.98  --add_important_lit                     false
% 2.51/0.98  --prop_solver_per_cl                    1000
% 2.51/0.98  --min_unsat_core                        false
% 2.51/0.98  --soft_assumptions                      false
% 2.51/0.98  --soft_lemma_size                       3
% 2.51/0.98  --prop_impl_unit_size                   0
% 2.51/0.98  --prop_impl_unit                        []
% 2.51/0.98  --share_sel_clauses                     true
% 2.51/0.98  --reset_solvers                         false
% 2.51/0.98  --bc_imp_inh                            [conj_cone]
% 2.51/0.98  --conj_cone_tolerance                   3.
% 2.51/0.98  --extra_neg_conj                        none
% 2.51/0.98  --large_theory_mode                     true
% 2.51/0.98  --prolific_symb_bound                   200
% 2.51/0.98  --lt_threshold                          2000
% 2.51/0.98  --clause_weak_htbl                      true
% 2.51/0.98  --gc_record_bc_elim                     false
% 2.51/0.98  
% 2.51/0.98  ------ Preprocessing Options
% 2.51/0.98  
% 2.51/0.98  --preprocessing_flag                    true
% 2.51/0.98  --time_out_prep_mult                    0.1
% 2.51/0.98  --splitting_mode                        input
% 2.51/0.98  --splitting_grd                         true
% 2.51/0.98  --splitting_cvd                         false
% 2.51/0.98  --splitting_cvd_svl                     false
% 2.51/0.98  --splitting_nvd                         32
% 2.51/0.98  --sub_typing                            true
% 2.51/0.98  --prep_gs_sim                           true
% 2.51/0.98  --prep_unflatten                        true
% 2.51/0.98  --prep_res_sim                          true
% 2.51/0.98  --prep_upred                            true
% 2.51/0.98  --prep_sem_filter                       exhaustive
% 2.51/0.98  --prep_sem_filter_out                   false
% 2.51/0.98  --pred_elim                             true
% 2.51/0.98  --res_sim_input                         true
% 2.51/0.98  --eq_ax_congr_red                       true
% 2.51/0.98  --pure_diseq_elim                       true
% 2.51/0.98  --brand_transform                       false
% 2.51/0.98  --non_eq_to_eq                          false
% 2.51/0.98  --prep_def_merge                        true
% 2.51/0.98  --prep_def_merge_prop_impl              false
% 2.51/0.98  --prep_def_merge_mbd                    true
% 2.51/0.98  --prep_def_merge_tr_red                 false
% 2.51/0.98  --prep_def_merge_tr_cl                  false
% 2.51/0.98  --smt_preprocessing                     true
% 2.51/0.98  --smt_ac_axioms                         fast
% 2.51/0.98  --preprocessed_out                      false
% 2.51/0.98  --preprocessed_stats                    false
% 2.51/0.98  
% 2.51/0.98  ------ Abstraction refinement Options
% 2.51/0.98  
% 2.51/0.98  --abstr_ref                             []
% 2.51/0.98  --abstr_ref_prep                        false
% 2.51/0.98  --abstr_ref_until_sat                   false
% 2.51/0.98  --abstr_ref_sig_restrict                funpre
% 2.51/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.51/0.98  --abstr_ref_under                       []
% 2.51/0.98  
% 2.51/0.98  ------ SAT Options
% 2.51/0.98  
% 2.51/0.98  --sat_mode                              false
% 2.51/0.98  --sat_fm_restart_options                ""
% 2.51/0.98  --sat_gr_def                            false
% 2.51/0.98  --sat_epr_types                         true
% 2.51/0.98  --sat_non_cyclic_types                  false
% 2.51/0.98  --sat_finite_models                     false
% 2.51/0.98  --sat_fm_lemmas                         false
% 2.51/0.98  --sat_fm_prep                           false
% 2.51/0.98  --sat_fm_uc_incr                        true
% 2.51/0.98  --sat_out_model                         small
% 2.51/0.98  --sat_out_clauses                       false
% 2.51/0.98  
% 2.51/0.98  ------ QBF Options
% 2.51/0.98  
% 2.51/0.98  --qbf_mode                              false
% 2.51/0.98  --qbf_elim_univ                         false
% 2.51/0.98  --qbf_dom_inst                          none
% 2.51/0.98  --qbf_dom_pre_inst                      false
% 2.51/0.98  --qbf_sk_in                             false
% 2.51/0.98  --qbf_pred_elim                         true
% 2.51/0.98  --qbf_split                             512
% 2.51/0.98  
% 2.51/0.98  ------ BMC1 Options
% 2.51/0.98  
% 2.51/0.98  --bmc1_incremental                      false
% 2.51/0.98  --bmc1_axioms                           reachable_all
% 2.51/0.98  --bmc1_min_bound                        0
% 2.51/0.98  --bmc1_max_bound                        -1
% 2.51/0.98  --bmc1_max_bound_default                -1
% 2.51/0.98  --bmc1_symbol_reachability              true
% 2.51/0.98  --bmc1_property_lemmas                  false
% 2.51/0.98  --bmc1_k_induction                      false
% 2.51/0.98  --bmc1_non_equiv_states                 false
% 2.51/0.98  --bmc1_deadlock                         false
% 2.51/0.98  --bmc1_ucm                              false
% 2.51/0.98  --bmc1_add_unsat_core                   none
% 2.51/0.98  --bmc1_unsat_core_children              false
% 2.51/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.51/0.98  --bmc1_out_stat                         full
% 2.51/0.98  --bmc1_ground_init                      false
% 2.51/0.98  --bmc1_pre_inst_next_state              false
% 2.51/0.98  --bmc1_pre_inst_state                   false
% 2.51/0.98  --bmc1_pre_inst_reach_state             false
% 2.51/0.98  --bmc1_out_unsat_core                   false
% 2.51/0.98  --bmc1_aig_witness_out                  false
% 2.51/0.98  --bmc1_verbose                          false
% 2.51/0.98  --bmc1_dump_clauses_tptp                false
% 2.51/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.51/0.98  --bmc1_dump_file                        -
% 2.51/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.51/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.51/0.98  --bmc1_ucm_extend_mode                  1
% 2.51/0.98  --bmc1_ucm_init_mode                    2
% 2.51/0.98  --bmc1_ucm_cone_mode                    none
% 2.51/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.51/0.98  --bmc1_ucm_relax_model                  4
% 2.51/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.51/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.51/0.98  --bmc1_ucm_layered_model                none
% 2.51/0.98  --bmc1_ucm_max_lemma_size               10
% 2.51/0.98  
% 2.51/0.98  ------ AIG Options
% 2.51/0.98  
% 2.51/0.98  --aig_mode                              false
% 2.51/0.98  
% 2.51/0.98  ------ Instantiation Options
% 2.51/0.98  
% 2.51/0.98  --instantiation_flag                    true
% 2.51/0.98  --inst_sos_flag                         false
% 2.51/0.98  --inst_sos_phase                        true
% 2.51/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.51/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.51/0.98  --inst_lit_sel_side                     none
% 2.51/0.98  --inst_solver_per_active                1400
% 2.51/0.98  --inst_solver_calls_frac                1.
% 2.51/0.98  --inst_passive_queue_type               priority_queues
% 2.51/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.51/0.98  --inst_passive_queues_freq              [25;2]
% 2.51/0.98  --inst_dismatching                      true
% 2.51/0.98  --inst_eager_unprocessed_to_passive     true
% 2.51/0.98  --inst_prop_sim_given                   true
% 2.51/0.98  --inst_prop_sim_new                     false
% 2.51/0.98  --inst_subs_new                         false
% 2.51/0.98  --inst_eq_res_simp                      false
% 2.51/0.98  --inst_subs_given                       false
% 2.51/0.98  --inst_orphan_elimination               true
% 2.51/0.98  --inst_learning_loop_flag               true
% 2.51/0.98  --inst_learning_start                   3000
% 2.51/0.98  --inst_learning_factor                  2
% 2.51/0.98  --inst_start_prop_sim_after_learn       3
% 2.51/0.98  --inst_sel_renew                        solver
% 2.51/0.98  --inst_lit_activity_flag                true
% 2.51/0.98  --inst_restr_to_given                   false
% 2.51/0.98  --inst_activity_threshold               500
% 2.51/0.98  --inst_out_proof                        true
% 2.51/0.98  
% 2.51/0.98  ------ Resolution Options
% 2.51/0.98  
% 2.51/0.98  --resolution_flag                       false
% 2.51/0.98  --res_lit_sel                           adaptive
% 2.51/0.98  --res_lit_sel_side                      none
% 2.51/0.98  --res_ordering                          kbo
% 2.51/0.98  --res_to_prop_solver                    active
% 2.51/0.98  --res_prop_simpl_new                    false
% 2.51/0.98  --res_prop_simpl_given                  true
% 2.51/0.98  --res_passive_queue_type                priority_queues
% 2.51/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.51/0.98  --res_passive_queues_freq               [15;5]
% 2.51/0.98  --res_forward_subs                      full
% 2.51/0.98  --res_backward_subs                     full
% 2.51/0.98  --res_forward_subs_resolution           true
% 2.51/0.98  --res_backward_subs_resolution          true
% 2.51/0.98  --res_orphan_elimination                true
% 2.51/0.98  --res_time_limit                        2.
% 2.51/0.98  --res_out_proof                         true
% 2.51/0.98  
% 2.51/0.98  ------ Superposition Options
% 2.51/0.98  
% 2.51/0.98  --superposition_flag                    true
% 2.51/0.98  --sup_passive_queue_type                priority_queues
% 2.51/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.51/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.51/0.98  --demod_completeness_check              fast
% 2.51/0.98  --demod_use_ground                      true
% 2.51/0.98  --sup_to_prop_solver                    passive
% 2.51/0.98  --sup_prop_simpl_new                    true
% 2.51/0.98  --sup_prop_simpl_given                  true
% 2.51/0.98  --sup_fun_splitting                     false
% 2.51/0.98  --sup_smt_interval                      50000
% 2.51/0.98  
% 2.51/0.98  ------ Superposition Simplification Setup
% 2.51/0.98  
% 2.51/0.98  --sup_indices_passive                   []
% 2.51/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.51/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.98  --sup_full_bw                           [BwDemod]
% 2.51/0.98  --sup_immed_triv                        [TrivRules]
% 2.51/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.51/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.98  --sup_immed_bw_main                     []
% 2.51/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.51/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/0.98  
% 2.51/0.98  ------ Combination Options
% 2.51/0.98  
% 2.51/0.98  --comb_res_mult                         3
% 2.51/0.98  --comb_sup_mult                         2
% 2.51/0.98  --comb_inst_mult                        10
% 2.51/0.98  
% 2.51/0.98  ------ Debug Options
% 2.51/0.98  
% 2.51/0.98  --dbg_backtrace                         false
% 2.51/0.98  --dbg_dump_prop_clauses                 false
% 2.51/0.98  --dbg_dump_prop_clauses_file            -
% 2.51/0.98  --dbg_out_stat                          false
% 2.51/0.98  
% 2.51/0.98  
% 2.51/0.98  
% 2.51/0.98  
% 2.51/0.98  ------ Proving...
% 2.51/0.98  
% 2.51/0.98  
% 2.51/0.98  % SZS status Theorem for theBenchmark.p
% 2.51/0.98  
% 2.51/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.51/0.98  
% 2.51/0.98  fof(f14,conjecture,(
% 2.51/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f15,negated_conjecture,(
% 2.51/0.98    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.51/0.98    inference(negated_conjecture,[],[f14])).
% 2.51/0.98  
% 2.51/0.98  fof(f35,plain,(
% 2.51/0.98    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 2.51/0.98    inference(ennf_transformation,[],[f15])).
% 2.51/0.98  
% 2.51/0.98  fof(f36,plain,(
% 2.51/0.98    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 2.51/0.98    inference(flattening,[],[f35])).
% 2.51/0.98  
% 2.51/0.98  fof(f42,plain,(
% 2.51/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k7_partfun1(X0,X4,k1_funct_1(X3,sK5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK5,X1))) )),
% 2.51/0.98    introduced(choice_axiom,[])).
% 2.51/0.98  
% 2.51/0.98  fof(f41,plain,(
% 2.51/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k7_partfun1(X0,sK4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4)) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK4))) )),
% 2.51/0.98    introduced(choice_axiom,[])).
% 2.51/0.98  
% 2.51/0.98  fof(f40,plain,(
% 2.51/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(sK3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK3,X1,X2) & v1_funct_1(sK3))) )),
% 2.51/0.98    introduced(choice_axiom,[])).
% 2.51/0.98  
% 2.51/0.98  fof(f39,plain,(
% 2.51/0.98    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 2.51/0.98    introduced(choice_axiom,[])).
% 2.51/0.98  
% 2.51/0.98  fof(f43,plain,(
% 2.51/0.98    (((k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 2.51/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f36,f42,f41,f40,f39])).
% 2.51/0.98  
% 2.51/0.98  fof(f71,plain,(
% 2.51/0.98    m1_subset_1(sK5,sK1)),
% 2.51/0.98    inference(cnf_transformation,[],[f43])).
% 2.51/0.98  
% 2.51/0.98  fof(f4,axiom,(
% 2.51/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f18,plain,(
% 2.51/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.51/0.98    inference(ennf_transformation,[],[f4])).
% 2.51/0.98  
% 2.51/0.98  fof(f19,plain,(
% 2.51/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.51/0.98    inference(flattening,[],[f18])).
% 2.51/0.98  
% 2.51/0.98  fof(f49,plain,(
% 2.51/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f19])).
% 2.51/0.98  
% 2.51/0.98  fof(f73,plain,(
% 2.51/0.98    k1_xboole_0 != sK1),
% 2.51/0.98    inference(cnf_transformation,[],[f43])).
% 2.51/0.98  
% 2.51/0.98  fof(f2,axiom,(
% 2.51/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f17,plain,(
% 2.51/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.51/0.98    inference(ennf_transformation,[],[f2])).
% 2.51/0.98  
% 2.51/0.98  fof(f45,plain,(
% 2.51/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f17])).
% 2.51/0.98  
% 2.51/0.98  fof(f70,plain,(
% 2.51/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 2.51/0.98    inference(cnf_transformation,[],[f43])).
% 2.51/0.98  
% 2.51/0.98  fof(f7,axiom,(
% 2.51/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f22,plain,(
% 2.51/0.98    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.51/0.98    inference(ennf_transformation,[],[f7])).
% 2.51/0.98  
% 2.51/0.98  fof(f52,plain,(
% 2.51/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.51/0.98    inference(cnf_transformation,[],[f22])).
% 2.51/0.98  
% 2.51/0.98  fof(f13,axiom,(
% 2.51/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f33,plain,(
% 2.51/0.98    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.51/0.98    inference(ennf_transformation,[],[f13])).
% 2.51/0.98  
% 2.51/0.98  fof(f34,plain,(
% 2.51/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.51/0.98    inference(flattening,[],[f33])).
% 2.51/0.98  
% 2.51/0.98  fof(f63,plain,(
% 2.51/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f34])).
% 2.51/0.98  
% 2.51/0.98  fof(f72,plain,(
% 2.51/0.98    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 2.51/0.98    inference(cnf_transformation,[],[f43])).
% 2.51/0.98  
% 2.51/0.98  fof(f65,plain,(
% 2.51/0.98    ~v1_xboole_0(sK2)),
% 2.51/0.98    inference(cnf_transformation,[],[f43])).
% 2.51/0.98  
% 2.51/0.98  fof(f66,plain,(
% 2.51/0.98    v1_funct_1(sK3)),
% 2.51/0.98    inference(cnf_transformation,[],[f43])).
% 2.51/0.98  
% 2.51/0.98  fof(f67,plain,(
% 2.51/0.98    v1_funct_2(sK3,sK1,sK2)),
% 2.51/0.98    inference(cnf_transformation,[],[f43])).
% 2.51/0.98  
% 2.51/0.98  fof(f68,plain,(
% 2.51/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.51/0.98    inference(cnf_transformation,[],[f43])).
% 2.51/0.98  
% 2.51/0.98  fof(f1,axiom,(
% 2.51/0.98    v1_xboole_0(k1_xboole_0)),
% 2.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f44,plain,(
% 2.51/0.98    v1_xboole_0(k1_xboole_0)),
% 2.51/0.98    inference(cnf_transformation,[],[f1])).
% 2.51/0.98  
% 2.51/0.98  fof(f12,axiom,(
% 2.51/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f31,plain,(
% 2.51/0.98    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.51/0.98    inference(ennf_transformation,[],[f12])).
% 2.51/0.98  
% 2.51/0.98  fof(f32,plain,(
% 2.51/0.98    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.51/0.98    inference(flattening,[],[f31])).
% 2.51/0.98  
% 2.51/0.98  fof(f58,plain,(
% 2.51/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f32])).
% 2.51/0.98  
% 2.51/0.98  fof(f61,plain,(
% 2.51/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f34])).
% 2.51/0.98  
% 2.51/0.98  fof(f6,axiom,(
% 2.51/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f16,plain,(
% 2.51/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.51/0.98    inference(pure_predicate_removal,[],[f6])).
% 2.51/0.98  
% 2.51/0.98  fof(f21,plain,(
% 2.51/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.51/0.98    inference(ennf_transformation,[],[f16])).
% 2.51/0.98  
% 2.51/0.98  fof(f51,plain,(
% 2.51/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.51/0.98    inference(cnf_transformation,[],[f21])).
% 2.51/0.98  
% 2.51/0.98  fof(f10,axiom,(
% 2.51/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 2.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f27,plain,(
% 2.51/0.98    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.51/0.98    inference(ennf_transformation,[],[f10])).
% 2.51/0.98  
% 2.51/0.98  fof(f28,plain,(
% 2.51/0.98    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.51/0.98    inference(flattening,[],[f27])).
% 2.51/0.98  
% 2.51/0.98  fof(f56,plain,(
% 2.51/0.98    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f28])).
% 2.51/0.98  
% 2.51/0.98  fof(f5,axiom,(
% 2.51/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f20,plain,(
% 2.51/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.51/0.98    inference(ennf_transformation,[],[f5])).
% 2.51/0.98  
% 2.51/0.98  fof(f50,plain,(
% 2.51/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.51/0.98    inference(cnf_transformation,[],[f20])).
% 2.51/0.98  
% 2.51/0.98  fof(f69,plain,(
% 2.51/0.98    v1_funct_1(sK4)),
% 2.51/0.98    inference(cnf_transformation,[],[f43])).
% 2.51/0.98  
% 2.51/0.98  fof(f11,axiom,(
% 2.51/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f29,plain,(
% 2.51/0.98    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.51/0.98    inference(ennf_transformation,[],[f11])).
% 2.51/0.98  
% 2.51/0.98  fof(f30,plain,(
% 2.51/0.98    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.51/0.98    inference(flattening,[],[f29])).
% 2.51/0.98  
% 2.51/0.98  fof(f57,plain,(
% 2.51/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f30])).
% 2.51/0.98  
% 2.51/0.98  fof(f3,axiom,(
% 2.51/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f37,plain,(
% 2.51/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.51/0.98    inference(nnf_transformation,[],[f3])).
% 2.51/0.98  
% 2.51/0.98  fof(f38,plain,(
% 2.51/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.51/0.98    inference(flattening,[],[f37])).
% 2.51/0.98  
% 2.51/0.98  fof(f46,plain,(
% 2.51/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f38])).
% 2.51/0.98  
% 2.51/0.98  fof(f47,plain,(
% 2.51/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.51/0.98    inference(cnf_transformation,[],[f38])).
% 2.51/0.98  
% 2.51/0.98  fof(f76,plain,(
% 2.51/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.51/0.98    inference(equality_resolution,[],[f47])).
% 2.51/0.98  
% 2.51/0.98  fof(f74,plain,(
% 2.51/0.98    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5)),
% 2.51/0.98    inference(cnf_transformation,[],[f43])).
% 2.51/0.98  
% 2.51/0.98  fof(f8,axiom,(
% 2.51/0.98    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 2.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f23,plain,(
% 2.51/0.98    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.51/0.98    inference(ennf_transformation,[],[f8])).
% 2.51/0.98  
% 2.51/0.98  fof(f24,plain,(
% 2.51/0.98    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.51/0.98    inference(flattening,[],[f23])).
% 2.51/0.98  
% 2.51/0.98  fof(f53,plain,(
% 2.51/0.98    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f24])).
% 2.51/0.98  
% 2.51/0.98  fof(f9,axiom,(
% 2.51/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f25,plain,(
% 2.51/0.98    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.51/0.98    inference(ennf_transformation,[],[f9])).
% 2.51/0.98  
% 2.51/0.98  fof(f26,plain,(
% 2.51/0.98    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.51/0.98    inference(flattening,[],[f25])).
% 2.51/0.98  
% 2.51/0.98  fof(f55,plain,(
% 2.51/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f26])).
% 2.51/0.98  
% 2.51/0.98  cnf(c_24,negated_conjecture,
% 2.51/0.98      ( m1_subset_1(sK5,sK1) ),
% 2.51/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1057,plain,
% 2.51/0.98      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_5,plain,
% 2.51/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.51/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1062,plain,
% 2.51/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 2.51/0.98      | r2_hidden(X0,X1) = iProver_top
% 2.51/0.98      | v1_xboole_0(X1) = iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_2821,plain,
% 2.51/0.98      ( r2_hidden(sK5,sK1) = iProver_top
% 2.51/0.98      | v1_xboole_0(sK1) = iProver_top ),
% 2.51/0.98      inference(superposition,[status(thm)],[c_1057,c_1062]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_37,plain,
% 2.51/0.98      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_22,negated_conjecture,
% 2.51/0.98      ( k1_xboole_0 != sK1 ),
% 2.51/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1,plain,
% 2.51/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.51/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1287,plain,
% 2.51/0.98      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 2.51/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1288,plain,
% 2.51/0.98      ( k1_xboole_0 = sK1 | v1_xboole_0(sK1) != iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_1287]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1375,plain,
% 2.51/0.98      ( ~ m1_subset_1(X0,sK1) | r2_hidden(X0,sK1) | v1_xboole_0(sK1) ),
% 2.51/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1669,plain,
% 2.51/0.98      ( ~ m1_subset_1(sK5,sK1) | r2_hidden(sK5,sK1) | v1_xboole_0(sK1) ),
% 2.51/0.98      inference(instantiation,[status(thm)],[c_1375]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1670,plain,
% 2.51/0.98      ( m1_subset_1(sK5,sK1) != iProver_top
% 2.51/0.98      | r2_hidden(sK5,sK1) = iProver_top
% 2.51/0.98      | v1_xboole_0(sK1) = iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_1669]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_2910,plain,
% 2.51/0.98      ( r2_hidden(sK5,sK1) = iProver_top ),
% 2.51/0.98      inference(global_propositional_subsumption,
% 2.51/0.98                [status(thm)],
% 2.51/0.98                [c_2821,c_37,c_22,c_1288,c_1670]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_25,negated_conjecture,
% 2.51/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 2.51/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1056,plain,
% 2.51/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_8,plain,
% 2.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.51/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.51/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1061,plain,
% 2.51/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.51/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_2066,plain,
% 2.51/0.98      ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
% 2.51/0.98      inference(superposition,[status(thm)],[c_1056,c_1061]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_16,plain,
% 2.51/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.51/0.98      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 2.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.51/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.51/0.98      | ~ v1_funct_1(X0)
% 2.51/0.98      | k1_xboole_0 = X2 ),
% 2.51/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_23,negated_conjecture,
% 2.51/0.98      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
% 2.51/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_449,plain,
% 2.51/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.51/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.51/0.98      | ~ v1_funct_1(X0)
% 2.51/0.98      | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
% 2.51/0.98      | k1_relset_1(sK2,sK0,sK4) != X3
% 2.51/0.98      | k1_xboole_0 = X2 ),
% 2.51/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_450,plain,
% 2.51/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.51/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_relset_1(sK2,sK0,sK4))))
% 2.51/0.98      | ~ v1_funct_1(X0)
% 2.51/0.98      | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
% 2.51/0.98      | k1_xboole_0 = X2 ),
% 2.51/0.98      inference(unflattening,[status(thm)],[c_449]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1045,plain,
% 2.51/0.98      ( k2_relset_1(X0,X1,X2) != k2_relset_1(sK1,sK2,sK3)
% 2.51/0.98      | k1_xboole_0 = X1
% 2.51/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.51/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.51/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relset_1(sK2,sK0,sK4)))) = iProver_top
% 2.51/0.98      | v1_funct_1(X2) != iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1448,plain,
% 2.51/0.98      ( sK2 = k1_xboole_0
% 2.51/0.98      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.51/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relset_1(sK2,sK0,sK4)))) = iProver_top
% 2.51/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.51/0.98      | v1_funct_1(sK3) != iProver_top ),
% 2.51/0.98      inference(equality_resolution,[status(thm)],[c_1045]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_30,negated_conjecture,
% 2.51/0.98      ( ~ v1_xboole_0(sK2) ),
% 2.51/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_29,negated_conjecture,
% 2.51/0.98      ( v1_funct_1(sK3) ),
% 2.51/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_32,plain,
% 2.51/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_28,negated_conjecture,
% 2.51/0.98      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.51/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_33,plain,
% 2.51/0.98      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_27,negated_conjecture,
% 2.51/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.51/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_34,plain,
% 2.51/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_0,plain,
% 2.51/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.51/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_670,plain,
% 2.51/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.51/0.98      theory(equality) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1295,plain,
% 2.51/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 != X0 ),
% 2.51/0.98      inference(instantiation,[status(thm)],[c_670]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1297,plain,
% 2.51/0.98      ( v1_xboole_0(sK2)
% 2.51/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 2.51/0.98      | sK2 != k1_xboole_0 ),
% 2.51/0.98      inference(instantiation,[status(thm)],[c_1295]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1807,plain,
% 2.51/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relset_1(sK2,sK0,sK4)))) = iProver_top ),
% 2.51/0.98      inference(global_propositional_subsumption,
% 2.51/0.98                [status(thm)],
% 2.51/0.98                [c_1448,c_30,c_32,c_33,c_34,c_0,c_1297]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_2220,plain,
% 2.51/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) = iProver_top ),
% 2.51/0.98      inference(demodulation,[status(thm)],[c_2066,c_1807]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_14,plain,
% 2.51/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.51/0.98      | ~ r2_hidden(X3,X1)
% 2.51/0.98      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.51/0.98      | ~ v1_funct_1(X0)
% 2.51/0.98      | k1_xboole_0 = X2 ),
% 2.51/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1058,plain,
% 2.51/0.98      ( k1_xboole_0 = X0
% 2.51/0.98      | v1_funct_2(X1,X2,X0) != iProver_top
% 2.51/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 2.51/0.98      | r2_hidden(X3,X2) != iProver_top
% 2.51/0.98      | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
% 2.51/0.98      | v1_funct_1(X1) != iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_3185,plain,
% 2.51/0.98      ( k1_relat_1(sK4) = k1_xboole_0
% 2.51/0.98      | v1_funct_2(sK3,sK1,k1_relat_1(sK4)) != iProver_top
% 2.51/0.98      | r2_hidden(X0,sK1) != iProver_top
% 2.51/0.98      | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
% 2.51/0.98      | v1_funct_1(sK3) != iProver_top ),
% 2.51/0.98      inference(superposition,[status(thm)],[c_2220,c_1058]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_18,plain,
% 2.51/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.51/0.98      | v1_funct_2(X0,X1,X3)
% 2.51/0.98      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 2.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.51/0.98      | ~ v1_funct_1(X0)
% 2.51/0.98      | k1_xboole_0 = X2 ),
% 2.51/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_426,plain,
% 2.51/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.51/0.98      | v1_funct_2(X0,X1,X3)
% 2.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.51/0.98      | ~ v1_funct_1(X0)
% 2.51/0.98      | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
% 2.51/0.98      | k1_relset_1(sK2,sK0,sK4) != X3
% 2.51/0.98      | k1_xboole_0 = X2 ),
% 2.51/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_427,plain,
% 2.51/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.51/0.98      | v1_funct_2(X0,X1,k1_relset_1(sK2,sK0,sK4))
% 2.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.51/0.98      | ~ v1_funct_1(X0)
% 2.51/0.98      | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
% 2.51/0.98      | k1_xboole_0 = X2 ),
% 2.51/0.98      inference(unflattening,[status(thm)],[c_426]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1046,plain,
% 2.51/0.98      ( k2_relset_1(X0,X1,X2) != k2_relset_1(sK1,sK2,sK3)
% 2.51/0.98      | k1_xboole_0 = X1
% 2.51/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.51/0.98      | v1_funct_2(X2,X0,k1_relset_1(sK2,sK0,sK4)) = iProver_top
% 2.51/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.51/0.98      | v1_funct_1(X2) != iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1710,plain,
% 2.51/0.98      ( sK2 = k1_xboole_0
% 2.51/0.98      | v1_funct_2(sK3,sK1,k1_relset_1(sK2,sK0,sK4)) = iProver_top
% 2.51/0.98      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.51/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.51/0.98      | v1_funct_1(sK3) != iProver_top ),
% 2.51/0.98      inference(equality_resolution,[status(thm)],[c_1046]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1779,plain,
% 2.51/0.98      ( v1_funct_2(sK3,sK1,k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
% 2.51/0.98      inference(global_propositional_subsumption,
% 2.51/0.98                [status(thm)],
% 2.51/0.98                [c_1710,c_30,c_32,c_33,c_34,c_0,c_1297]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_2221,plain,
% 2.51/0.98      ( v1_funct_2(sK3,sK1,k1_relat_1(sK4)) = iProver_top ),
% 2.51/0.98      inference(demodulation,[status(thm)],[c_2066,c_1779]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_4264,plain,
% 2.51/0.98      ( r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
% 2.51/0.98      | r2_hidden(X0,sK1) != iProver_top
% 2.51/0.98      | k1_relat_1(sK4) = k1_xboole_0 ),
% 2.51/0.98      inference(global_propositional_subsumption,
% 2.51/0.98                [status(thm)],
% 2.51/0.98                [c_3185,c_32,c_2221]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_4265,plain,
% 2.51/0.98      ( k1_relat_1(sK4) = k1_xboole_0
% 2.51/0.98      | r2_hidden(X0,sK1) != iProver_top
% 2.51/0.98      | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top ),
% 2.51/0.98      inference(renaming,[status(thm)],[c_4264]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_7,plain,
% 2.51/0.98      ( v5_relat_1(X0,X1)
% 2.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.51/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_12,plain,
% 2.51/0.98      ( ~ v5_relat_1(X0,X1)
% 2.51/0.98      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.51/0.98      | ~ v1_funct_1(X0)
% 2.51/0.98      | ~ v1_relat_1(X0)
% 2.51/0.98      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.51/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_289,plain,
% 2.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.51/0.98      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.51/0.98      | ~ v1_funct_1(X0)
% 2.51/0.98      | ~ v1_relat_1(X0)
% 2.51/0.98      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.51/0.98      inference(resolution,[status(thm)],[c_7,c_12]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_6,plain,
% 2.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.51/0.98      | v1_relat_1(X0) ),
% 2.51/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_293,plain,
% 2.51/0.98      ( ~ v1_funct_1(X0)
% 2.51/0.98      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.51/0.98      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.51/0.98      inference(global_propositional_subsumption,
% 2.51/0.98                [status(thm)],
% 2.51/0.98                [c_289,c_6]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_294,plain,
% 2.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.51/0.98      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.51/0.98      | ~ v1_funct_1(X0)
% 2.51/0.98      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.51/0.98      inference(renaming,[status(thm)],[c_293]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1050,plain,
% 2.51/0.98      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 2.51/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 2.51/0.98      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 2.51/0.98      | v1_funct_1(X1) != iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1895,plain,
% 2.51/0.98      ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
% 2.51/0.98      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.51/0.98      | v1_funct_1(sK4) != iProver_top ),
% 2.51/0.98      inference(superposition,[status(thm)],[c_1056,c_1050]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_26,negated_conjecture,
% 2.51/0.98      ( v1_funct_1(sK4) ),
% 2.51/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_35,plain,
% 2.51/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_2551,plain,
% 2.51/0.98      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.51/0.98      | k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0) ),
% 2.51/0.98      inference(global_propositional_subsumption,
% 2.51/0.98                [status(thm)],
% 2.51/0.98                [c_1895,c_35]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_2552,plain,
% 2.51/0.98      ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
% 2.51/0.98      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.51/0.98      inference(renaming,[status(thm)],[c_2551]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_4274,plain,
% 2.51/0.98      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.51/0.98      | k1_relat_1(sK4) = k1_xboole_0
% 2.51/0.98      | r2_hidden(X0,sK1) != iProver_top ),
% 2.51/0.98      inference(superposition,[status(thm)],[c_4265,c_2552]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_4510,plain,
% 2.51/0.98      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 2.51/0.98      | k1_relat_1(sK4) = k1_xboole_0 ),
% 2.51/0.98      inference(superposition,[status(thm)],[c_2910,c_4274]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_13,plain,
% 2.51/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.51/0.98      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 2.51/0.98      | ~ m1_subset_1(X5,X1)
% 2.51/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.51/0.98      | ~ v1_funct_1(X4)
% 2.51/0.98      | ~ v1_funct_1(X0)
% 2.51/0.98      | v1_xboole_0(X2)
% 2.51/0.98      | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k1_funct_1(X4,k1_funct_1(X0,X5))
% 2.51/0.98      | k1_xboole_0 = X1 ),
% 2.51/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_348,plain,
% 2.51/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.51/0.98      | ~ m1_subset_1(X3,X1)
% 2.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.51/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 2.51/0.98      | ~ v1_funct_1(X0)
% 2.51/0.98      | ~ v1_funct_1(X4)
% 2.51/0.98      | v1_xboole_0(X2)
% 2.51/0.98      | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
% 2.51/0.98      | k1_relset_1(X2,X5,X4) != k1_relset_1(sK2,sK0,sK4)
% 2.51/0.99      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 2.51/0.99      | k1_xboole_0 = X1 ),
% 2.51/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_1049,plain,
% 2.51/0.99      ( k2_relset_1(X0,X1,X2) != k2_relset_1(sK1,sK2,sK3)
% 2.51/0.99      | k1_relset_1(X1,X3,X4) != k1_relset_1(sK2,sK0,sK4)
% 2.51/0.99      | k1_funct_1(k8_funct_2(X0,X1,X3,X2,X4),X5) = k1_funct_1(X4,k1_funct_1(X2,X5))
% 2.51/0.99      | k1_xboole_0 = X0
% 2.51/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.51/0.99      | m1_subset_1(X5,X0) != iProver_top
% 2.51/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.51/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 2.51/0.99      | v1_funct_1(X2) != iProver_top
% 2.51/0.99      | v1_funct_1(X4) != iProver_top
% 2.51/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.51/0.99      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_1724,plain,
% 2.51/0.99      ( k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
% 2.51/0.99      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.51/0.99      | sK1 = k1_xboole_0
% 2.51/0.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.51/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 2.51/0.99      | m1_subset_1(X2,sK1) != iProver_top
% 2.51/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.51/0.99      | v1_funct_1(X1) != iProver_top
% 2.51/0.99      | v1_funct_1(sK3) != iProver_top
% 2.51/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 2.51/0.99      inference(equality_resolution,[status(thm)],[c_1049]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_31,plain,
% 2.51/0.99      ( v1_xboole_0(sK2) != iProver_top ),
% 2.51/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_4,plain,
% 2.51/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.51/0.99      | k1_xboole_0 = X0
% 2.51/0.99      | k1_xboole_0 = X1 ),
% 2.51/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_71,plain,
% 2.51/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.51/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 2.51/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_3,plain,
% 2.51/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.51/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_72,plain,
% 2.51/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.51/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_669,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_1317,plain,
% 2.51/0.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 2.51/0.99      inference(instantiation,[status(thm)],[c_669]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_1318,plain,
% 2.51/0.99      ( sK1 != k1_xboole_0
% 2.51/0.99      | k1_xboole_0 = sK1
% 2.51/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.51/0.99      inference(instantiation,[status(thm)],[c_1317]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_1813,plain,
% 2.51/0.99      ( m1_subset_1(X2,sK1) != iProver_top
% 2.51/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 2.51/0.99      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.51/0.99      | k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
% 2.51/0.99      | v1_funct_1(X1) != iProver_top ),
% 2.51/0.99      inference(global_propositional_subsumption,
% 2.51/0.99                [status(thm)],
% 2.51/0.99                [c_1724,c_31,c_32,c_33,c_34,c_22,c_71,c_72,c_1318]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_1814,plain,
% 2.51/0.99      ( k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
% 2.51/0.99      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.51/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 2.51/0.99      | m1_subset_1(X2,sK1) != iProver_top
% 2.51/0.99      | v1_funct_1(X1) != iProver_top ),
% 2.51/0.99      inference(renaming,[status(thm)],[c_1813]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_1824,plain,
% 2.51/0.99      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.51/0.99      | m1_subset_1(X0,sK1) != iProver_top
% 2.51/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 2.51/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.51/0.99      inference(equality_resolution,[status(thm)],[c_1814]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_36,plain,
% 2.51/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.51/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_1881,plain,
% 2.51/0.99      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.51/0.99      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.51/0.99      inference(global_propositional_subsumption,
% 2.51/0.99                [status(thm)],
% 2.51/0.99                [c_1824,c_35,c_36]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_1889,plain,
% 2.51/0.99      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.51/0.99      inference(superposition,[status(thm)],[c_1057,c_1881]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_21,negated_conjecture,
% 2.51/0.99      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
% 2.51/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_2407,plain,
% 2.51/0.99      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.51/0.99      inference(demodulation,[status(thm)],[c_1889,c_21]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_4533,plain,
% 2.51/0.99      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 2.51/0.99      inference(global_propositional_subsumption,
% 2.51/0.99                [status(thm)],
% 2.51/0.99                [c_4510,c_2407]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_9,plain,
% 2.51/0.99      ( ~ v1_partfun1(X0,X1)
% 2.51/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.51/0.99      | ~ v1_xboole_0(X2)
% 2.51/0.99      | v1_xboole_0(X1) ),
% 2.51/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_1060,plain,
% 2.51/0.99      ( v1_partfun1(X0,X1) != iProver_top
% 2.51/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.51/0.99      | v1_xboole_0(X2) != iProver_top
% 2.51/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.51/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_3184,plain,
% 2.51/0.99      ( v1_partfun1(sK3,sK1) != iProver_top
% 2.51/0.99      | v1_xboole_0(k1_relat_1(sK4)) != iProver_top
% 2.51/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 2.51/0.99      inference(superposition,[status(thm)],[c_2220,c_1060]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_10,plain,
% 2.51/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.51/0.99      | v1_partfun1(X0,X1)
% 2.51/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.51/0.99      | ~ v1_funct_1(X0)
% 2.51/0.99      | v1_xboole_0(X2) ),
% 2.51/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_1347,plain,
% 2.51/0.99      ( ~ v1_funct_2(X0,X1,sK2)
% 2.51/0.99      | v1_partfun1(X0,X1)
% 2.51/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 2.51/0.99      | ~ v1_funct_1(X0)
% 2.51/0.99      | v1_xboole_0(sK2) ),
% 2.51/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_1544,plain,
% 2.51/0.99      ( ~ v1_funct_2(sK3,X0,sK2)
% 2.51/0.99      | v1_partfun1(sK3,X0)
% 2.51/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 2.51/0.99      | ~ v1_funct_1(sK3)
% 2.51/0.99      | v1_xboole_0(sK2) ),
% 2.51/0.99      inference(instantiation,[status(thm)],[c_1347]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_1769,plain,
% 2.51/0.99      ( ~ v1_funct_2(sK3,sK1,sK2)
% 2.51/0.99      | v1_partfun1(sK3,sK1)
% 2.51/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.51/0.99      | ~ v1_funct_1(sK3)
% 2.51/0.99      | v1_xboole_0(sK2) ),
% 2.51/0.99      inference(instantiation,[status(thm)],[c_1544]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_1770,plain,
% 2.51/0.99      ( v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.51/0.99      | v1_partfun1(sK3,sK1) = iProver_top
% 2.51/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.51/0.99      | v1_funct_1(sK3) != iProver_top
% 2.51/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 2.51/0.99      inference(predicate_to_equality,[status(thm)],[c_1769]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_4253,plain,
% 2.51/0.99      ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top ),
% 2.51/0.99      inference(global_propositional_subsumption,
% 2.51/0.99                [status(thm)],
% 2.51/0.99                [c_3184,c_31,c_32,c_33,c_34,c_22,c_1288,c_1770]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_4537,plain,
% 2.51/0.99      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.51/0.99      inference(demodulation,[status(thm)],[c_4533,c_4253]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(c_76,plain,
% 2.51/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.51/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.51/0.99  
% 2.51/0.99  cnf(contradiction,plain,
% 2.51/0.99      ( $false ),
% 2.51/0.99      inference(minisat,[status(thm)],[c_4537,c_76]) ).
% 2.51/0.99  
% 2.51/0.99  
% 2.51/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.51/0.99  
% 2.51/0.99  ------                               Statistics
% 2.51/0.99  
% 2.51/0.99  ------ General
% 2.51/0.99  
% 2.51/0.99  abstr_ref_over_cycles:                  0
% 2.51/0.99  abstr_ref_under_cycles:                 0
% 2.51/0.99  gc_basic_clause_elim:                   0
% 2.51/0.99  forced_gc_time:                         0
% 2.51/0.99  parsing_time:                           0.011
% 2.51/0.99  unif_index_cands_time:                  0.
% 2.51/0.99  unif_index_add_time:                    0.
% 2.51/0.99  orderings_time:                         0.
% 2.51/0.99  out_proof_time:                         0.011
% 2.51/0.99  total_time:                             0.208
% 2.51/0.99  num_of_symbols:                         55
% 2.51/0.99  num_of_terms:                           7677
% 2.51/0.99  
% 2.51/0.99  ------ Preprocessing
% 2.51/0.99  
% 2.51/0.99  num_of_splits:                          0
% 2.51/0.99  num_of_split_atoms:                     0
% 2.51/0.99  num_of_reused_defs:                     0
% 2.51/0.99  num_eq_ax_congr_red:                    12
% 2.51/0.99  num_of_sem_filtered_clauses:            1
% 2.51/0.99  num_of_subtypes:                        0
% 2.51/0.99  monotx_restored_types:                  0
% 2.51/0.99  sat_num_of_epr_types:                   0
% 2.51/0.99  sat_num_of_non_cyclic_types:            0
% 2.51/0.99  sat_guarded_non_collapsed_types:        0
% 2.51/0.99  num_pure_diseq_elim:                    0
% 2.51/0.99  simp_replaced_by:                       0
% 2.51/0.99  res_preprocessed:                       132
% 2.51/0.99  prep_upred:                             0
% 2.51/0.99  prep_unflattend:                        4
% 2.51/0.99  smt_new_axioms:                         0
% 2.51/0.99  pred_elim_cands:                        6
% 2.51/0.99  pred_elim:                              3
% 2.51/0.99  pred_elim_cl:                           3
% 2.51/0.99  pred_elim_cycles:                       7
% 2.51/0.99  merged_defs:                            0
% 2.51/0.99  merged_defs_ncl:                        0
% 2.51/0.99  bin_hyper_res:                          0
% 2.51/0.99  prep_cycles:                            4
% 2.51/0.99  pred_elim_time:                         0.007
% 2.51/0.99  splitting_time:                         0.
% 2.51/0.99  sem_filter_time:                        0.
% 2.51/0.99  monotx_time:                            0.001
% 2.51/0.99  subtype_inf_time:                       0.
% 2.51/0.99  
% 2.51/0.99  ------ Problem properties
% 2.51/0.99  
% 2.51/0.99  clauses:                                25
% 2.51/0.99  conjectures:                            9
% 2.51/0.99  epr:                                    9
% 2.51/0.99  horn:                                   18
% 2.51/0.99  ground:                                 10
% 2.51/0.99  unary:                                  12
% 2.51/0.99  binary:                                 2
% 2.51/0.99  lits:                                   74
% 2.51/0.99  lits_eq:                                21
% 2.51/0.99  fd_pure:                                0
% 2.51/0.99  fd_pseudo:                              0
% 2.51/0.99  fd_cond:                                6
% 2.51/0.99  fd_pseudo_cond:                         0
% 2.51/0.99  ac_symbols:                             0
% 2.51/0.99  
% 2.51/0.99  ------ Propositional Solver
% 2.51/0.99  
% 2.51/0.99  prop_solver_calls:                      28
% 2.51/0.99  prop_fast_solver_calls:                 1118
% 2.51/0.99  smt_solver_calls:                       0
% 2.51/0.99  smt_fast_solver_calls:                  0
% 2.51/0.99  prop_num_of_clauses:                    1829
% 2.51/0.99  prop_preprocess_simplified:             4991
% 2.51/0.99  prop_fo_subsumed:                       38
% 2.51/0.99  prop_solver_time:                       0.
% 2.51/0.99  smt_solver_time:                        0.
% 2.51/0.99  smt_fast_solver_time:                   0.
% 2.51/0.99  prop_fast_solver_time:                  0.
% 2.51/0.99  prop_unsat_core_time:                   0.
% 2.51/0.99  
% 2.51/0.99  ------ QBF
% 2.51/0.99  
% 2.51/0.99  qbf_q_res:                              0
% 2.51/0.99  qbf_num_tautologies:                    0
% 2.51/0.99  qbf_prep_cycles:                        0
% 2.51/0.99  
% 2.51/0.99  ------ BMC1
% 2.51/0.99  
% 2.51/0.99  bmc1_current_bound:                     -1
% 2.51/0.99  bmc1_last_solved_bound:                 -1
% 2.51/0.99  bmc1_unsat_core_size:                   -1
% 2.51/0.99  bmc1_unsat_core_parents_size:           -1
% 2.51/0.99  bmc1_merge_next_fun:                    0
% 2.51/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.51/0.99  
% 2.51/0.99  ------ Instantiation
% 2.51/0.99  
% 2.51/0.99  inst_num_of_clauses:                    639
% 2.51/0.99  inst_num_in_passive:                    31
% 2.51/0.99  inst_num_in_active:                     311
% 2.51/0.99  inst_num_in_unprocessed:                297
% 2.51/0.99  inst_num_of_loops:                      320
% 2.51/0.99  inst_num_of_learning_restarts:          0
% 2.51/0.99  inst_num_moves_active_passive:          6
% 2.51/0.99  inst_lit_activity:                      0
% 2.51/0.99  inst_lit_activity_moves:                0
% 2.51/0.99  inst_num_tautologies:                   0
% 2.51/0.99  inst_num_prop_implied:                  0
% 2.51/0.99  inst_num_existing_simplified:           0
% 2.51/0.99  inst_num_eq_res_simplified:             0
% 2.51/0.99  inst_num_child_elim:                    0
% 2.51/0.99  inst_num_of_dismatching_blockings:      114
% 2.51/0.99  inst_num_of_non_proper_insts:           420
% 2.51/0.99  inst_num_of_duplicates:                 0
% 2.51/0.99  inst_inst_num_from_inst_to_res:         0
% 2.51/0.99  inst_dismatching_checking_time:         0.
% 2.51/0.99  
% 2.51/0.99  ------ Resolution
% 2.51/0.99  
% 2.51/0.99  res_num_of_clauses:                     0
% 2.51/0.99  res_num_in_passive:                     0
% 2.51/0.99  res_num_in_active:                      0
% 2.51/0.99  res_num_of_loops:                       136
% 2.51/0.99  res_forward_subset_subsumed:            47
% 2.51/0.99  res_backward_subset_subsumed:           0
% 2.51/0.99  res_forward_subsumed:                   0
% 2.51/0.99  res_backward_subsumed:                  0
% 2.51/0.99  res_forward_subsumption_resolution:     0
% 2.51/0.99  res_backward_subsumption_resolution:    0
% 2.51/0.99  res_clause_to_clause_subsumption:       148
% 2.51/0.99  res_orphan_elimination:                 0
% 2.51/0.99  res_tautology_del:                      22
% 2.51/0.99  res_num_eq_res_simplified:              0
% 2.51/0.99  res_num_sel_changes:                    0
% 2.51/0.99  res_moves_from_active_to_pass:          0
% 2.51/0.99  
% 2.51/0.99  ------ Superposition
% 2.51/0.99  
% 2.51/0.99  sup_time_total:                         0.
% 2.51/0.99  sup_time_generating:                    0.
% 2.51/0.99  sup_time_sim_full:                      0.
% 2.51/0.99  sup_time_sim_immed:                     0.
% 2.51/0.99  
% 2.51/0.99  sup_num_of_clauses:                     49
% 2.51/0.99  sup_num_in_active:                      40
% 2.51/0.99  sup_num_in_passive:                     9
% 2.51/0.99  sup_num_of_loops:                       63
% 2.51/0.99  sup_fw_superposition:                   35
% 2.51/0.99  sup_bw_superposition:                   10
% 2.51/0.99  sup_immediate_simplified:               7
% 2.51/0.99  sup_given_eliminated:                   0
% 2.51/0.99  comparisons_done:                       0
% 2.51/0.99  comparisons_avoided:                    9
% 2.51/0.99  
% 2.51/0.99  ------ Simplifications
% 2.51/0.99  
% 2.51/0.99  
% 2.51/0.99  sim_fw_subset_subsumed:                 5
% 2.51/0.99  sim_bw_subset_subsumed:                 2
% 2.51/0.99  sim_fw_subsumed:                        1
% 2.51/0.99  sim_bw_subsumed:                        0
% 2.51/0.99  sim_fw_subsumption_res:                 0
% 2.51/0.99  sim_bw_subsumption_res:                 0
% 2.51/0.99  sim_tautology_del:                      1
% 2.51/0.99  sim_eq_tautology_del:                   5
% 2.51/0.99  sim_eq_res_simp:                        0
% 2.51/0.99  sim_fw_demodulated:                     3
% 2.51/0.99  sim_bw_demodulated:                     23
% 2.51/0.99  sim_light_normalised:                   4
% 2.51/0.99  sim_joinable_taut:                      0
% 2.51/0.99  sim_joinable_simp:                      0
% 2.51/0.99  sim_ac_normalised:                      0
% 2.51/0.99  sim_smt_subsumption:                    0
% 2.51/0.99  
%------------------------------------------------------------------------------

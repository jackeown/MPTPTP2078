%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:57 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 634 expanded)
%              Number of clauses        :   96 ( 176 expanded)
%              Number of leaves         :   20 ( 215 expanded)
%              Depth                    :   20
%              Number of atoms          :  532 (4779 expanded)
%              Number of equality atoms :  184 (1215 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f33,f38,f37,f36,f35])).

fof(f60,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f54,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

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

fof(f28,plain,(
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
    inference(flattening,[],[f28])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1658,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1665,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2495,plain,
    ( r2_hidden(sK5,sK1) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1658,c_1665])).

cnf(c_30,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1850,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | r2_hidden(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1851,plain,
    ( m1_subset_1(sK5,sK1) != iProver_top
    | r2_hidden(sK5,sK1) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1850])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1930,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1931,plain,
    ( k1_xboole_0 = sK1
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1930])).

cnf(c_2618,plain,
    ( r2_hidden(sK5,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2495,c_30,c_15,c_1851,c_1931])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1657,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1660,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2477,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1657,c_1660])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1659,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2553,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2477,c_1659])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_324,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | sK2 != X2
    | sK1 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_325,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ r2_hidden(X0,sK1)
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_329,plain,
    ( r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3))
    | ~ r2_hidden(X0,sK1)
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_22,c_20])).

cnf(c_330,plain,
    ( ~ r2_hidden(X0,sK1)
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3))
    | k1_xboole_0 = sK2 ),
    inference(renaming,[status(thm)],[c_329])).

cnf(c_1652,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_330])).

cnf(c_331,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_330])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_411,plain,
    ( sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_23])).

cnf(c_1112,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1141,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1112])).

cnf(c_1113,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2029,plain,
    ( X0 != X1
    | X0 = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1113])).

cnf(c_2030,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2029])).

cnf(c_2332,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1652,c_331,c_411,c_1141,c_2030])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1664,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1662,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2825,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X2,X1) = iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1664,c_1662])).

cnf(c_3354,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) != iProver_top
    | m1_subset_1(k1_funct_1(sK3,X1),X0) = iProver_top
    | r2_hidden(X1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2332,c_2825])).

cnf(c_3731,plain,
    ( m1_subset_1(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2553,c_3354])).

cnf(c_3815,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
    | v1_xboole_0(k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3731,c_1665])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_161,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_213,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_161])).

cnf(c_1654,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_213])).

cnf(c_3223,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) != iProver_top
    | r2_hidden(X1,sK1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2332,c_1654])).

cnf(c_3564,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | v1_xboole_0(k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2553,c_3223])).

cnf(c_3571,plain,
    ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2618,c_3564])).

cnf(c_3970,plain,
    ( r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3815,c_3571])).

cnf(c_3971,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3970])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_298,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_9,c_11])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_298,c_19])).

cnf(c_491,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k7_partfun1(X1,sK4,X2) = k1_funct_1(sK4,X2) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_1649,plain,
    ( k7_partfun1(X0,sK4,X1) = k1_funct_1(sK4,X1)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_1998,plain,
    ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1657,c_1649])).

cnf(c_29,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1827,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1828,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK0)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1827])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_214,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_161])).

cnf(c_1833,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_2137,plain,
    ( ~ r1_tarski(sK4,k2_zfmisc_1(sK2,sK0))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1833])).

cnf(c_2138,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2137])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2187,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2188,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2187])).

cnf(c_2197,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1998,c_29,c_1828,c_2138,c_2188])).

cnf(c_2198,plain,
    ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2197])).

cnf(c_3980,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3971,c_2198])).

cnf(c_4227,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_2618,c_3980])).

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
    inference(cnf_transformation,[],[f52])).

cnf(c_345,plain,
    ( ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,X4))
    | ~ m1_subset_1(X5,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | k1_funct_1(k8_funct_2(X0,X1,X3,X2,X4),X5) = k1_funct_1(X4,k1_funct_1(X2,X5))
    | sK2 != X1
    | sK1 != X0
    | sK3 != X2
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_346,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(X2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_350,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_346,c_23,c_22,c_20,c_15])).

cnf(c_351,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(X2,sK1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) ),
    inference(renaming,[status(thm)],[c_350])).

cnf(c_454,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(X2,sK1)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_351,c_19])).

cnf(c_455,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,sK4))
    | ~ m1_subset_1(X1,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,sK4),X1) = k1_funct_1(sK4,k1_funct_1(sK3,X1)) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_1651,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,sK4),X1) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,sK4)) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_2259,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1659,c_1651])).

cnf(c_2264,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2259,c_29])).

cnf(c_2265,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2264])).

cnf(c_2272,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1658,c_2265])).

cnf(c_14,negated_conjecture,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2330,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_2272,c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4227,c_2330])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:32:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.19/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.00  
% 2.19/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.19/1.00  
% 2.19/1.00  ------  iProver source info
% 2.19/1.00  
% 2.19/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.19/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.19/1.00  git: non_committed_changes: false
% 2.19/1.00  git: last_make_outside_of_git: false
% 2.19/1.00  
% 2.19/1.00  ------ 
% 2.19/1.00  
% 2.19/1.00  ------ Input Options
% 2.19/1.00  
% 2.19/1.00  --out_options                           all
% 2.19/1.00  --tptp_safe_out                         true
% 2.19/1.00  --problem_path                          ""
% 2.19/1.00  --include_path                          ""
% 2.19/1.00  --clausifier                            res/vclausify_rel
% 2.19/1.00  --clausifier_options                    --mode clausify
% 2.19/1.00  --stdin                                 false
% 2.19/1.00  --stats_out                             all
% 2.19/1.00  
% 2.19/1.00  ------ General Options
% 2.19/1.00  
% 2.19/1.00  --fof                                   false
% 2.19/1.00  --time_out_real                         305.
% 2.19/1.00  --time_out_virtual                      -1.
% 2.19/1.00  --symbol_type_check                     false
% 2.19/1.00  --clausify_out                          false
% 2.19/1.00  --sig_cnt_out                           false
% 2.19/1.00  --trig_cnt_out                          false
% 2.19/1.00  --trig_cnt_out_tolerance                1.
% 2.19/1.00  --trig_cnt_out_sk_spl                   false
% 2.19/1.00  --abstr_cl_out                          false
% 2.19/1.00  
% 2.19/1.00  ------ Global Options
% 2.19/1.00  
% 2.19/1.00  --schedule                              default
% 2.19/1.00  --add_important_lit                     false
% 2.19/1.00  --prop_solver_per_cl                    1000
% 2.19/1.00  --min_unsat_core                        false
% 2.19/1.00  --soft_assumptions                      false
% 2.19/1.00  --soft_lemma_size                       3
% 2.19/1.00  --prop_impl_unit_size                   0
% 2.19/1.00  --prop_impl_unit                        []
% 2.19/1.00  --share_sel_clauses                     true
% 2.19/1.00  --reset_solvers                         false
% 2.19/1.00  --bc_imp_inh                            [conj_cone]
% 2.19/1.00  --conj_cone_tolerance                   3.
% 2.19/1.00  --extra_neg_conj                        none
% 2.19/1.00  --large_theory_mode                     true
% 2.19/1.00  --prolific_symb_bound                   200
% 2.19/1.00  --lt_threshold                          2000
% 2.19/1.00  --clause_weak_htbl                      true
% 2.19/1.00  --gc_record_bc_elim                     false
% 2.19/1.00  
% 2.19/1.00  ------ Preprocessing Options
% 2.19/1.00  
% 2.19/1.00  --preprocessing_flag                    true
% 2.19/1.00  --time_out_prep_mult                    0.1
% 2.19/1.00  --splitting_mode                        input
% 2.19/1.00  --splitting_grd                         true
% 2.19/1.00  --splitting_cvd                         false
% 2.19/1.00  --splitting_cvd_svl                     false
% 2.19/1.00  --splitting_nvd                         32
% 2.19/1.00  --sub_typing                            true
% 2.19/1.00  --prep_gs_sim                           true
% 2.19/1.00  --prep_unflatten                        true
% 2.19/1.00  --prep_res_sim                          true
% 2.19/1.00  --prep_upred                            true
% 2.19/1.00  --prep_sem_filter                       exhaustive
% 2.19/1.00  --prep_sem_filter_out                   false
% 2.19/1.00  --pred_elim                             true
% 2.19/1.00  --res_sim_input                         true
% 2.19/1.00  --eq_ax_congr_red                       true
% 2.19/1.00  --pure_diseq_elim                       true
% 2.19/1.00  --brand_transform                       false
% 2.19/1.00  --non_eq_to_eq                          false
% 2.19/1.00  --prep_def_merge                        true
% 2.19/1.00  --prep_def_merge_prop_impl              false
% 2.19/1.00  --prep_def_merge_mbd                    true
% 2.19/1.00  --prep_def_merge_tr_red                 false
% 2.19/1.00  --prep_def_merge_tr_cl                  false
% 2.19/1.00  --smt_preprocessing                     true
% 2.19/1.00  --smt_ac_axioms                         fast
% 2.19/1.00  --preprocessed_out                      false
% 2.19/1.00  --preprocessed_stats                    false
% 2.19/1.00  
% 2.19/1.00  ------ Abstraction refinement Options
% 2.19/1.00  
% 2.19/1.00  --abstr_ref                             []
% 2.19/1.00  --abstr_ref_prep                        false
% 2.19/1.00  --abstr_ref_until_sat                   false
% 2.19/1.00  --abstr_ref_sig_restrict                funpre
% 2.19/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/1.00  --abstr_ref_under                       []
% 2.19/1.00  
% 2.19/1.00  ------ SAT Options
% 2.19/1.00  
% 2.19/1.00  --sat_mode                              false
% 2.19/1.00  --sat_fm_restart_options                ""
% 2.19/1.00  --sat_gr_def                            false
% 2.19/1.00  --sat_epr_types                         true
% 2.19/1.00  --sat_non_cyclic_types                  false
% 2.19/1.00  --sat_finite_models                     false
% 2.19/1.00  --sat_fm_lemmas                         false
% 2.19/1.00  --sat_fm_prep                           false
% 2.19/1.00  --sat_fm_uc_incr                        true
% 2.19/1.00  --sat_out_model                         small
% 2.19/1.00  --sat_out_clauses                       false
% 2.19/1.00  
% 2.19/1.00  ------ QBF Options
% 2.19/1.00  
% 2.19/1.00  --qbf_mode                              false
% 2.19/1.00  --qbf_elim_univ                         false
% 2.19/1.00  --qbf_dom_inst                          none
% 2.19/1.00  --qbf_dom_pre_inst                      false
% 2.19/1.00  --qbf_sk_in                             false
% 2.19/1.00  --qbf_pred_elim                         true
% 2.19/1.00  --qbf_split                             512
% 2.19/1.00  
% 2.19/1.00  ------ BMC1 Options
% 2.19/1.00  
% 2.19/1.00  --bmc1_incremental                      false
% 2.19/1.00  --bmc1_axioms                           reachable_all
% 2.19/1.00  --bmc1_min_bound                        0
% 2.19/1.00  --bmc1_max_bound                        -1
% 2.19/1.00  --bmc1_max_bound_default                -1
% 2.19/1.00  --bmc1_symbol_reachability              true
% 2.19/1.00  --bmc1_property_lemmas                  false
% 2.19/1.00  --bmc1_k_induction                      false
% 2.19/1.00  --bmc1_non_equiv_states                 false
% 2.19/1.00  --bmc1_deadlock                         false
% 2.19/1.00  --bmc1_ucm                              false
% 2.19/1.00  --bmc1_add_unsat_core                   none
% 2.19/1.00  --bmc1_unsat_core_children              false
% 2.19/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/1.00  --bmc1_out_stat                         full
% 2.19/1.00  --bmc1_ground_init                      false
% 2.19/1.00  --bmc1_pre_inst_next_state              false
% 2.19/1.00  --bmc1_pre_inst_state                   false
% 2.19/1.00  --bmc1_pre_inst_reach_state             false
% 2.19/1.00  --bmc1_out_unsat_core                   false
% 2.19/1.00  --bmc1_aig_witness_out                  false
% 2.19/1.00  --bmc1_verbose                          false
% 2.19/1.00  --bmc1_dump_clauses_tptp                false
% 2.19/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.19/1.00  --bmc1_dump_file                        -
% 2.19/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.19/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.19/1.00  --bmc1_ucm_extend_mode                  1
% 2.19/1.00  --bmc1_ucm_init_mode                    2
% 2.19/1.00  --bmc1_ucm_cone_mode                    none
% 2.19/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.19/1.00  --bmc1_ucm_relax_model                  4
% 2.19/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.19/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/1.00  --bmc1_ucm_layered_model                none
% 2.19/1.00  --bmc1_ucm_max_lemma_size               10
% 2.19/1.00  
% 2.19/1.00  ------ AIG Options
% 2.19/1.00  
% 2.19/1.00  --aig_mode                              false
% 2.19/1.00  
% 2.19/1.00  ------ Instantiation Options
% 2.19/1.00  
% 2.19/1.00  --instantiation_flag                    true
% 2.19/1.00  --inst_sos_flag                         false
% 2.19/1.00  --inst_sos_phase                        true
% 2.19/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/1.00  --inst_lit_sel_side                     num_symb
% 2.19/1.00  --inst_solver_per_active                1400
% 2.19/1.00  --inst_solver_calls_frac                1.
% 2.19/1.00  --inst_passive_queue_type               priority_queues
% 2.19/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/1.00  --inst_passive_queues_freq              [25;2]
% 2.19/1.00  --inst_dismatching                      true
% 2.19/1.00  --inst_eager_unprocessed_to_passive     true
% 2.19/1.00  --inst_prop_sim_given                   true
% 2.19/1.00  --inst_prop_sim_new                     false
% 2.19/1.00  --inst_subs_new                         false
% 2.19/1.00  --inst_eq_res_simp                      false
% 2.19/1.00  --inst_subs_given                       false
% 2.19/1.00  --inst_orphan_elimination               true
% 2.19/1.00  --inst_learning_loop_flag               true
% 2.19/1.00  --inst_learning_start                   3000
% 2.19/1.00  --inst_learning_factor                  2
% 2.19/1.00  --inst_start_prop_sim_after_learn       3
% 2.19/1.00  --inst_sel_renew                        solver
% 2.19/1.00  --inst_lit_activity_flag                true
% 2.19/1.00  --inst_restr_to_given                   false
% 2.19/1.00  --inst_activity_threshold               500
% 2.19/1.00  --inst_out_proof                        true
% 2.19/1.00  
% 2.19/1.00  ------ Resolution Options
% 2.19/1.00  
% 2.19/1.00  --resolution_flag                       true
% 2.19/1.00  --res_lit_sel                           adaptive
% 2.19/1.00  --res_lit_sel_side                      none
% 2.19/1.00  --res_ordering                          kbo
% 2.19/1.00  --res_to_prop_solver                    active
% 2.19/1.00  --res_prop_simpl_new                    false
% 2.19/1.00  --res_prop_simpl_given                  true
% 2.19/1.00  --res_passive_queue_type                priority_queues
% 2.19/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/1.00  --res_passive_queues_freq               [15;5]
% 2.19/1.00  --res_forward_subs                      full
% 2.19/1.00  --res_backward_subs                     full
% 2.19/1.00  --res_forward_subs_resolution           true
% 2.19/1.00  --res_backward_subs_resolution          true
% 2.19/1.00  --res_orphan_elimination                true
% 2.19/1.00  --res_time_limit                        2.
% 2.19/1.00  --res_out_proof                         true
% 2.19/1.00  
% 2.19/1.00  ------ Superposition Options
% 2.19/1.00  
% 2.19/1.00  --superposition_flag                    true
% 2.19/1.00  --sup_passive_queue_type                priority_queues
% 2.19/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.19/1.00  --demod_completeness_check              fast
% 2.19/1.00  --demod_use_ground                      true
% 2.19/1.00  --sup_to_prop_solver                    passive
% 2.19/1.00  --sup_prop_simpl_new                    true
% 2.19/1.00  --sup_prop_simpl_given                  true
% 2.19/1.00  --sup_fun_splitting                     false
% 2.19/1.00  --sup_smt_interval                      50000
% 2.19/1.00  
% 2.19/1.00  ------ Superposition Simplification Setup
% 2.19/1.00  
% 2.19/1.00  --sup_indices_passive                   []
% 2.19/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.00  --sup_full_bw                           [BwDemod]
% 2.19/1.00  --sup_immed_triv                        [TrivRules]
% 2.19/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.00  --sup_immed_bw_main                     []
% 2.19/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.00  
% 2.19/1.00  ------ Combination Options
% 2.19/1.00  
% 2.19/1.00  --comb_res_mult                         3
% 2.19/1.00  --comb_sup_mult                         2
% 2.19/1.00  --comb_inst_mult                        10
% 2.19/1.00  
% 2.19/1.00  ------ Debug Options
% 2.19/1.00  
% 2.19/1.00  --dbg_backtrace                         false
% 2.19/1.00  --dbg_dump_prop_clauses                 false
% 2.19/1.00  --dbg_dump_prop_clauses_file            -
% 2.19/1.00  --dbg_out_stat                          false
% 2.19/1.00  ------ Parsing...
% 2.19/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.19/1.00  
% 2.19/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.19/1.00  
% 2.19/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.19/1.00  
% 2.19/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.19/1.00  ------ Proving...
% 2.19/1.00  ------ Problem Properties 
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  clauses                                 22
% 2.19/1.00  conjectures                             7
% 2.19/1.00  EPR                                     8
% 2.19/1.00  Horn                                    20
% 2.19/1.00  unary                                   9
% 2.19/1.00  binary                                  4
% 2.19/1.00  lits                                    48
% 2.19/1.00  lits eq                                 9
% 2.19/1.00  fd_pure                                 0
% 2.19/1.00  fd_pseudo                               0
% 2.19/1.00  fd_cond                                 1
% 2.19/1.00  fd_pseudo_cond                          0
% 2.19/1.00  AC symbols                              0
% 2.19/1.00  
% 2.19/1.00  ------ Schedule dynamic 5 is on 
% 2.19/1.00  
% 2.19/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  ------ 
% 2.19/1.00  Current options:
% 2.19/1.00  ------ 
% 2.19/1.00  
% 2.19/1.00  ------ Input Options
% 2.19/1.00  
% 2.19/1.00  --out_options                           all
% 2.19/1.00  --tptp_safe_out                         true
% 2.19/1.00  --problem_path                          ""
% 2.19/1.00  --include_path                          ""
% 2.19/1.00  --clausifier                            res/vclausify_rel
% 2.19/1.00  --clausifier_options                    --mode clausify
% 2.19/1.00  --stdin                                 false
% 2.19/1.00  --stats_out                             all
% 2.19/1.00  
% 2.19/1.00  ------ General Options
% 2.19/1.00  
% 2.19/1.00  --fof                                   false
% 2.19/1.00  --time_out_real                         305.
% 2.19/1.00  --time_out_virtual                      -1.
% 2.19/1.00  --symbol_type_check                     false
% 2.19/1.00  --clausify_out                          false
% 2.19/1.00  --sig_cnt_out                           false
% 2.19/1.00  --trig_cnt_out                          false
% 2.19/1.00  --trig_cnt_out_tolerance                1.
% 2.19/1.00  --trig_cnt_out_sk_spl                   false
% 2.19/1.00  --abstr_cl_out                          false
% 2.19/1.00  
% 2.19/1.00  ------ Global Options
% 2.19/1.00  
% 2.19/1.00  --schedule                              default
% 2.19/1.00  --add_important_lit                     false
% 2.19/1.00  --prop_solver_per_cl                    1000
% 2.19/1.00  --min_unsat_core                        false
% 2.19/1.00  --soft_assumptions                      false
% 2.19/1.00  --soft_lemma_size                       3
% 2.19/1.00  --prop_impl_unit_size                   0
% 2.19/1.00  --prop_impl_unit                        []
% 2.19/1.00  --share_sel_clauses                     true
% 2.19/1.00  --reset_solvers                         false
% 2.19/1.00  --bc_imp_inh                            [conj_cone]
% 2.19/1.00  --conj_cone_tolerance                   3.
% 2.19/1.00  --extra_neg_conj                        none
% 2.19/1.00  --large_theory_mode                     true
% 2.19/1.00  --prolific_symb_bound                   200
% 2.19/1.00  --lt_threshold                          2000
% 2.19/1.00  --clause_weak_htbl                      true
% 2.19/1.00  --gc_record_bc_elim                     false
% 2.19/1.00  
% 2.19/1.00  ------ Preprocessing Options
% 2.19/1.00  
% 2.19/1.00  --preprocessing_flag                    true
% 2.19/1.00  --time_out_prep_mult                    0.1
% 2.19/1.00  --splitting_mode                        input
% 2.19/1.00  --splitting_grd                         true
% 2.19/1.00  --splitting_cvd                         false
% 2.19/1.00  --splitting_cvd_svl                     false
% 2.19/1.00  --splitting_nvd                         32
% 2.19/1.00  --sub_typing                            true
% 2.19/1.00  --prep_gs_sim                           true
% 2.19/1.00  --prep_unflatten                        true
% 2.19/1.00  --prep_res_sim                          true
% 2.19/1.00  --prep_upred                            true
% 2.19/1.00  --prep_sem_filter                       exhaustive
% 2.19/1.00  --prep_sem_filter_out                   false
% 2.19/1.00  --pred_elim                             true
% 2.19/1.00  --res_sim_input                         true
% 2.19/1.00  --eq_ax_congr_red                       true
% 2.19/1.00  --pure_diseq_elim                       true
% 2.19/1.00  --brand_transform                       false
% 2.19/1.00  --non_eq_to_eq                          false
% 2.19/1.00  --prep_def_merge                        true
% 2.19/1.00  --prep_def_merge_prop_impl              false
% 2.19/1.00  --prep_def_merge_mbd                    true
% 2.19/1.00  --prep_def_merge_tr_red                 false
% 2.19/1.00  --prep_def_merge_tr_cl                  false
% 2.19/1.00  --smt_preprocessing                     true
% 2.19/1.00  --smt_ac_axioms                         fast
% 2.19/1.00  --preprocessed_out                      false
% 2.19/1.00  --preprocessed_stats                    false
% 2.19/1.00  
% 2.19/1.00  ------ Abstraction refinement Options
% 2.19/1.00  
% 2.19/1.00  --abstr_ref                             []
% 2.19/1.00  --abstr_ref_prep                        false
% 2.19/1.00  --abstr_ref_until_sat                   false
% 2.19/1.00  --abstr_ref_sig_restrict                funpre
% 2.19/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/1.00  --abstr_ref_under                       []
% 2.19/1.00  
% 2.19/1.00  ------ SAT Options
% 2.19/1.00  
% 2.19/1.00  --sat_mode                              false
% 2.19/1.00  --sat_fm_restart_options                ""
% 2.19/1.00  --sat_gr_def                            false
% 2.19/1.00  --sat_epr_types                         true
% 2.19/1.00  --sat_non_cyclic_types                  false
% 2.19/1.00  --sat_finite_models                     false
% 2.19/1.00  --sat_fm_lemmas                         false
% 2.19/1.00  --sat_fm_prep                           false
% 2.19/1.00  --sat_fm_uc_incr                        true
% 2.19/1.00  --sat_out_model                         small
% 2.19/1.00  --sat_out_clauses                       false
% 2.19/1.00  
% 2.19/1.00  ------ QBF Options
% 2.19/1.00  
% 2.19/1.00  --qbf_mode                              false
% 2.19/1.00  --qbf_elim_univ                         false
% 2.19/1.00  --qbf_dom_inst                          none
% 2.19/1.00  --qbf_dom_pre_inst                      false
% 2.19/1.00  --qbf_sk_in                             false
% 2.19/1.00  --qbf_pred_elim                         true
% 2.19/1.00  --qbf_split                             512
% 2.19/1.00  
% 2.19/1.00  ------ BMC1 Options
% 2.19/1.00  
% 2.19/1.00  --bmc1_incremental                      false
% 2.19/1.00  --bmc1_axioms                           reachable_all
% 2.19/1.00  --bmc1_min_bound                        0
% 2.19/1.00  --bmc1_max_bound                        -1
% 2.19/1.00  --bmc1_max_bound_default                -1
% 2.19/1.00  --bmc1_symbol_reachability              true
% 2.19/1.00  --bmc1_property_lemmas                  false
% 2.19/1.00  --bmc1_k_induction                      false
% 2.19/1.00  --bmc1_non_equiv_states                 false
% 2.19/1.00  --bmc1_deadlock                         false
% 2.19/1.00  --bmc1_ucm                              false
% 2.19/1.00  --bmc1_add_unsat_core                   none
% 2.19/1.00  --bmc1_unsat_core_children              false
% 2.19/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/1.00  --bmc1_out_stat                         full
% 2.19/1.00  --bmc1_ground_init                      false
% 2.19/1.00  --bmc1_pre_inst_next_state              false
% 2.19/1.00  --bmc1_pre_inst_state                   false
% 2.19/1.00  --bmc1_pre_inst_reach_state             false
% 2.19/1.00  --bmc1_out_unsat_core                   false
% 2.19/1.00  --bmc1_aig_witness_out                  false
% 2.19/1.00  --bmc1_verbose                          false
% 2.19/1.00  --bmc1_dump_clauses_tptp                false
% 2.19/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.19/1.00  --bmc1_dump_file                        -
% 2.19/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.19/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.19/1.00  --bmc1_ucm_extend_mode                  1
% 2.19/1.00  --bmc1_ucm_init_mode                    2
% 2.19/1.00  --bmc1_ucm_cone_mode                    none
% 2.19/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.19/1.00  --bmc1_ucm_relax_model                  4
% 2.19/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.19/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/1.00  --bmc1_ucm_layered_model                none
% 2.19/1.00  --bmc1_ucm_max_lemma_size               10
% 2.19/1.00  
% 2.19/1.00  ------ AIG Options
% 2.19/1.00  
% 2.19/1.00  --aig_mode                              false
% 2.19/1.00  
% 2.19/1.00  ------ Instantiation Options
% 2.19/1.00  
% 2.19/1.00  --instantiation_flag                    true
% 2.19/1.00  --inst_sos_flag                         false
% 2.19/1.00  --inst_sos_phase                        true
% 2.19/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/1.00  --inst_lit_sel_side                     none
% 2.19/1.00  --inst_solver_per_active                1400
% 2.19/1.00  --inst_solver_calls_frac                1.
% 2.19/1.00  --inst_passive_queue_type               priority_queues
% 2.19/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/1.00  --inst_passive_queues_freq              [25;2]
% 2.19/1.00  --inst_dismatching                      true
% 2.19/1.00  --inst_eager_unprocessed_to_passive     true
% 2.19/1.00  --inst_prop_sim_given                   true
% 2.19/1.00  --inst_prop_sim_new                     false
% 2.19/1.00  --inst_subs_new                         false
% 2.19/1.00  --inst_eq_res_simp                      false
% 2.19/1.00  --inst_subs_given                       false
% 2.19/1.00  --inst_orphan_elimination               true
% 2.19/1.00  --inst_learning_loop_flag               true
% 2.19/1.00  --inst_learning_start                   3000
% 2.19/1.00  --inst_learning_factor                  2
% 2.19/1.00  --inst_start_prop_sim_after_learn       3
% 2.19/1.00  --inst_sel_renew                        solver
% 2.19/1.00  --inst_lit_activity_flag                true
% 2.19/1.00  --inst_restr_to_given                   false
% 2.19/1.00  --inst_activity_threshold               500
% 2.19/1.00  --inst_out_proof                        true
% 2.19/1.00  
% 2.19/1.00  ------ Resolution Options
% 2.19/1.00  
% 2.19/1.00  --resolution_flag                       false
% 2.19/1.00  --res_lit_sel                           adaptive
% 2.19/1.00  --res_lit_sel_side                      none
% 2.19/1.00  --res_ordering                          kbo
% 2.19/1.00  --res_to_prop_solver                    active
% 2.19/1.00  --res_prop_simpl_new                    false
% 2.19/1.00  --res_prop_simpl_given                  true
% 2.19/1.00  --res_passive_queue_type                priority_queues
% 2.19/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/1.00  --res_passive_queues_freq               [15;5]
% 2.19/1.00  --res_forward_subs                      full
% 2.19/1.00  --res_backward_subs                     full
% 2.19/1.00  --res_forward_subs_resolution           true
% 2.19/1.00  --res_backward_subs_resolution          true
% 2.19/1.00  --res_orphan_elimination                true
% 2.19/1.00  --res_time_limit                        2.
% 2.19/1.00  --res_out_proof                         true
% 2.19/1.00  
% 2.19/1.00  ------ Superposition Options
% 2.19/1.00  
% 2.19/1.00  --superposition_flag                    true
% 2.19/1.00  --sup_passive_queue_type                priority_queues
% 2.19/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.19/1.00  --demod_completeness_check              fast
% 2.19/1.00  --demod_use_ground                      true
% 2.19/1.00  --sup_to_prop_solver                    passive
% 2.19/1.00  --sup_prop_simpl_new                    true
% 2.19/1.00  --sup_prop_simpl_given                  true
% 2.19/1.00  --sup_fun_splitting                     false
% 2.19/1.00  --sup_smt_interval                      50000
% 2.19/1.00  
% 2.19/1.00  ------ Superposition Simplification Setup
% 2.19/1.00  
% 2.19/1.00  --sup_indices_passive                   []
% 2.19/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.00  --sup_full_bw                           [BwDemod]
% 2.19/1.00  --sup_immed_triv                        [TrivRules]
% 2.19/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.00  --sup_immed_bw_main                     []
% 2.19/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.00  
% 2.19/1.00  ------ Combination Options
% 2.19/1.00  
% 2.19/1.00  --comb_res_mult                         3
% 2.19/1.00  --comb_sup_mult                         2
% 2.19/1.00  --comb_inst_mult                        10
% 2.19/1.00  
% 2.19/1.00  ------ Debug Options
% 2.19/1.00  
% 2.19/1.00  --dbg_backtrace                         false
% 2.19/1.00  --dbg_dump_prop_clauses                 false
% 2.19/1.00  --dbg_dump_prop_clauses_file            -
% 2.19/1.00  --dbg_out_stat                          false
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  ------ Proving...
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  % SZS status Theorem for theBenchmark.p
% 2.19/1.00  
% 2.19/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.19/1.00  
% 2.19/1.00  fof(f14,conjecture,(
% 2.19/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.19/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f15,negated_conjecture,(
% 2.19/1.00    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.19/1.00    inference(negated_conjecture,[],[f14])).
% 2.19/1.00  
% 2.19/1.00  fof(f32,plain,(
% 2.19/1.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 2.19/1.00    inference(ennf_transformation,[],[f15])).
% 2.19/1.00  
% 2.19/1.00  fof(f33,plain,(
% 2.19/1.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 2.19/1.00    inference(flattening,[],[f32])).
% 2.19/1.00  
% 2.19/1.00  fof(f38,plain,(
% 2.19/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k7_partfun1(X0,X4,k1_funct_1(X3,sK5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK5,X1))) )),
% 2.19/1.00    introduced(choice_axiom,[])).
% 2.19/1.00  
% 2.19/1.00  fof(f37,plain,(
% 2.19/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k7_partfun1(X0,sK4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4)) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK4))) )),
% 2.19/1.00    introduced(choice_axiom,[])).
% 2.19/1.00  
% 2.19/1.00  fof(f36,plain,(
% 2.19/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(sK3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK3,X1,X2) & v1_funct_1(sK3))) )),
% 2.19/1.00    introduced(choice_axiom,[])).
% 2.19/1.00  
% 2.19/1.00  fof(f35,plain,(
% 2.19/1.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 2.19/1.00    introduced(choice_axiom,[])).
% 2.19/1.00  
% 2.19/1.00  fof(f39,plain,(
% 2.19/1.00    (((k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 2.19/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f33,f38,f37,f36,f35])).
% 2.19/1.00  
% 2.19/1.00  fof(f60,plain,(
% 2.19/1.00    m1_subset_1(sK5,sK1)),
% 2.19/1.00    inference(cnf_transformation,[],[f39])).
% 2.19/1.00  
% 2.19/1.00  fof(f3,axiom,(
% 2.19/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.19/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f18,plain,(
% 2.19/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.19/1.00    inference(ennf_transformation,[],[f3])).
% 2.19/1.00  
% 2.19/1.00  fof(f19,plain,(
% 2.19/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.19/1.00    inference(flattening,[],[f18])).
% 2.19/1.00  
% 2.19/1.00  fof(f42,plain,(
% 2.19/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f19])).
% 2.19/1.00  
% 2.19/1.00  fof(f62,plain,(
% 2.19/1.00    k1_xboole_0 != sK1),
% 2.19/1.00    inference(cnf_transformation,[],[f39])).
% 2.19/1.00  
% 2.19/1.00  fof(f2,axiom,(
% 2.19/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.19/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f17,plain,(
% 2.19/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.19/1.00    inference(ennf_transformation,[],[f2])).
% 2.19/1.00  
% 2.19/1.00  fof(f41,plain,(
% 2.19/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f17])).
% 2.19/1.00  
% 2.19/1.00  fof(f59,plain,(
% 2.19/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 2.19/1.00    inference(cnf_transformation,[],[f39])).
% 2.19/1.00  
% 2.19/1.00  fof(f10,axiom,(
% 2.19/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.19/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f25,plain,(
% 2.19/1.00    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/1.00    inference(ennf_transformation,[],[f10])).
% 2.19/1.00  
% 2.19/1.00  fof(f50,plain,(
% 2.19/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.19/1.00    inference(cnf_transformation,[],[f25])).
% 2.19/1.00  
% 2.19/1.00  fof(f61,plain,(
% 2.19/1.00    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 2.19/1.00    inference(cnf_transformation,[],[f39])).
% 2.19/1.00  
% 2.19/1.00  fof(f13,axiom,(
% 2.19/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 2.19/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f30,plain,(
% 2.19/1.00    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.19/1.00    inference(ennf_transformation,[],[f13])).
% 2.19/1.00  
% 2.19/1.00  fof(f31,plain,(
% 2.19/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.19/1.00    inference(flattening,[],[f30])).
% 2.19/1.00  
% 2.19/1.00  fof(f53,plain,(
% 2.19/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f31])).
% 2.19/1.00  
% 2.19/1.00  fof(f56,plain,(
% 2.19/1.00    v1_funct_2(sK3,sK1,sK2)),
% 2.19/1.00    inference(cnf_transformation,[],[f39])).
% 2.19/1.00  
% 2.19/1.00  fof(f55,plain,(
% 2.19/1.00    v1_funct_1(sK3)),
% 2.19/1.00    inference(cnf_transformation,[],[f39])).
% 2.19/1.00  
% 2.19/1.00  fof(f57,plain,(
% 2.19/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.19/1.00    inference(cnf_transformation,[],[f39])).
% 2.19/1.00  
% 2.19/1.00  fof(f1,axiom,(
% 2.19/1.00    v1_xboole_0(k1_xboole_0)),
% 2.19/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f40,plain,(
% 2.19/1.00    v1_xboole_0(k1_xboole_0)),
% 2.19/1.00    inference(cnf_transformation,[],[f1])).
% 2.19/1.00  
% 2.19/1.00  fof(f54,plain,(
% 2.19/1.00    ~v1_xboole_0(sK2)),
% 2.19/1.00    inference(cnf_transformation,[],[f39])).
% 2.19/1.00  
% 2.19/1.00  fof(f4,axiom,(
% 2.19/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.19/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f34,plain,(
% 2.19/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.19/1.00    inference(nnf_transformation,[],[f4])).
% 2.19/1.00  
% 2.19/1.00  fof(f44,plain,(
% 2.19/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f34])).
% 2.19/1.00  
% 2.19/1.00  fof(f5,axiom,(
% 2.19/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.19/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f20,plain,(
% 2.19/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.19/1.00    inference(ennf_transformation,[],[f5])).
% 2.19/1.00  
% 2.19/1.00  fof(f21,plain,(
% 2.19/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.19/1.00    inference(flattening,[],[f20])).
% 2.19/1.00  
% 2.19/1.00  fof(f45,plain,(
% 2.19/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f21])).
% 2.19/1.00  
% 2.19/1.00  fof(f6,axiom,(
% 2.19/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.19/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f22,plain,(
% 2.19/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.19/1.00    inference(ennf_transformation,[],[f6])).
% 2.19/1.00  
% 2.19/1.00  fof(f46,plain,(
% 2.19/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f22])).
% 2.19/1.00  
% 2.19/1.00  fof(f9,axiom,(
% 2.19/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.19/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f16,plain,(
% 2.19/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.19/1.00    inference(pure_predicate_removal,[],[f9])).
% 2.19/1.00  
% 2.19/1.00  fof(f24,plain,(
% 2.19/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/1.00    inference(ennf_transformation,[],[f16])).
% 2.19/1.00  
% 2.19/1.00  fof(f49,plain,(
% 2.19/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.19/1.00    inference(cnf_transformation,[],[f24])).
% 2.19/1.00  
% 2.19/1.00  fof(f11,axiom,(
% 2.19/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 2.19/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f26,plain,(
% 2.19/1.00    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.19/1.00    inference(ennf_transformation,[],[f11])).
% 2.19/1.00  
% 2.19/1.00  fof(f27,plain,(
% 2.19/1.00    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.19/1.00    inference(flattening,[],[f26])).
% 2.19/1.00  
% 2.19/1.00  fof(f51,plain,(
% 2.19/1.00    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f27])).
% 2.19/1.00  
% 2.19/1.00  fof(f58,plain,(
% 2.19/1.00    v1_funct_1(sK4)),
% 2.19/1.00    inference(cnf_transformation,[],[f39])).
% 2.19/1.00  
% 2.19/1.00  fof(f43,plain,(
% 2.19/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.19/1.00    inference(cnf_transformation,[],[f34])).
% 2.19/1.00  
% 2.19/1.00  fof(f7,axiom,(
% 2.19/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.19/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f23,plain,(
% 2.19/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.19/1.00    inference(ennf_transformation,[],[f7])).
% 2.19/1.00  
% 2.19/1.00  fof(f47,plain,(
% 2.19/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f23])).
% 2.19/1.00  
% 2.19/1.00  fof(f8,axiom,(
% 2.19/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.19/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f48,plain,(
% 2.19/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.19/1.00    inference(cnf_transformation,[],[f8])).
% 2.19/1.00  
% 2.19/1.00  fof(f12,axiom,(
% 2.19/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.19/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f28,plain,(
% 2.19/1.00    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.19/1.00    inference(ennf_transformation,[],[f12])).
% 2.19/1.00  
% 2.19/1.00  fof(f29,plain,(
% 2.19/1.00    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.19/1.00    inference(flattening,[],[f28])).
% 2.19/1.00  
% 2.19/1.00  fof(f52,plain,(
% 2.19/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f29])).
% 2.19/1.00  
% 2.19/1.00  fof(f63,plain,(
% 2.19/1.00    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5)),
% 2.19/1.00    inference(cnf_transformation,[],[f39])).
% 2.19/1.00  
% 2.19/1.00  cnf(c_17,negated_conjecture,
% 2.19/1.00      ( m1_subset_1(sK5,sK1) ),
% 2.19/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1658,plain,
% 2.19/1.00      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2,plain,
% 2.19/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.19/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1665,plain,
% 2.19/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 2.19/1.00      | r2_hidden(X0,X1) = iProver_top
% 2.19/1.00      | v1_xboole_0(X1) = iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2495,plain,
% 2.19/1.00      ( r2_hidden(sK5,sK1) = iProver_top
% 2.19/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_1658,c_1665]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_30,plain,
% 2.19/1.00      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_15,negated_conjecture,
% 2.19/1.00      ( k1_xboole_0 != sK1 ),
% 2.19/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1850,plain,
% 2.19/1.00      ( ~ m1_subset_1(sK5,sK1) | r2_hidden(sK5,sK1) | v1_xboole_0(sK1) ),
% 2.19/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1851,plain,
% 2.19/1.00      ( m1_subset_1(sK5,sK1) != iProver_top
% 2.19/1.00      | r2_hidden(sK5,sK1) = iProver_top
% 2.19/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_1850]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1,plain,
% 2.19/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.19/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1930,plain,
% 2.19/1.00      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 2.19/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1931,plain,
% 2.19/1.00      ( k1_xboole_0 = sK1 | v1_xboole_0(sK1) != iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_1930]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2618,plain,
% 2.19/1.00      ( r2_hidden(sK5,sK1) = iProver_top ),
% 2.19/1.00      inference(global_propositional_subsumption,
% 2.19/1.00                [status(thm)],
% 2.19/1.00                [c_2495,c_30,c_15,c_1851,c_1931]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_18,negated_conjecture,
% 2.19/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 2.19/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1657,plain,
% 2.19/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_10,plain,
% 2.19/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.19/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1660,plain,
% 2.19/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.19/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2477,plain,
% 2.19/1.00      ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_1657,c_1660]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_16,negated_conjecture,
% 2.19/1.00      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
% 2.19/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1659,plain,
% 2.19/1.00      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2553,plain,
% 2.19/1.00      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) = iProver_top ),
% 2.19/1.00      inference(demodulation,[status(thm)],[c_2477,c_1659]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_13,plain,
% 2.19/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/1.00      | ~ r2_hidden(X3,X1)
% 2.19/1.00      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 2.19/1.00      | ~ v1_funct_1(X0)
% 2.19/1.00      | k1_xboole_0 = X2 ),
% 2.19/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_21,negated_conjecture,
% 2.19/1.00      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.19/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_324,plain,
% 2.19/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/1.00      | ~ r2_hidden(X3,X1)
% 2.19/1.00      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 2.19/1.00      | ~ v1_funct_1(X0)
% 2.19/1.00      | sK2 != X2
% 2.19/1.00      | sK1 != X1
% 2.19/1.00      | sK3 != X0
% 2.19/1.00      | k1_xboole_0 = X2 ),
% 2.19/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_325,plain,
% 2.19/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.19/1.00      | ~ r2_hidden(X0,sK1)
% 2.19/1.00      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3))
% 2.19/1.00      | ~ v1_funct_1(sK3)
% 2.19/1.00      | k1_xboole_0 = sK2 ),
% 2.19/1.00      inference(unflattening,[status(thm)],[c_324]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_22,negated_conjecture,
% 2.19/1.00      ( v1_funct_1(sK3) ),
% 2.19/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_20,negated_conjecture,
% 2.19/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.19/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_329,plain,
% 2.19/1.00      ( r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3))
% 2.19/1.00      | ~ r2_hidden(X0,sK1)
% 2.19/1.00      | k1_xboole_0 = sK2 ),
% 2.19/1.00      inference(global_propositional_subsumption,
% 2.19/1.00                [status(thm)],
% 2.19/1.00                [c_325,c_22,c_20]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_330,plain,
% 2.19/1.00      ( ~ r2_hidden(X0,sK1)
% 2.19/1.00      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3))
% 2.19/1.00      | k1_xboole_0 = sK2 ),
% 2.19/1.00      inference(renaming,[status(thm)],[c_329]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1652,plain,
% 2.19/1.00      ( k1_xboole_0 = sK2
% 2.19/1.00      | r2_hidden(X0,sK1) != iProver_top
% 2.19/1.00      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3)) = iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_330]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_331,plain,
% 2.19/1.00      ( k1_xboole_0 = sK2
% 2.19/1.00      | r2_hidden(X0,sK1) != iProver_top
% 2.19/1.00      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3)) = iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_330]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_0,plain,
% 2.19/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.19/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_23,negated_conjecture,
% 2.19/1.00      ( ~ v1_xboole_0(sK2) ),
% 2.19/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_411,plain,
% 2.19/1.00      ( sK2 != k1_xboole_0 ),
% 2.19/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_23]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1112,plain,( X0 = X0 ),theory(equality) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1141,plain,
% 2.19/1.00      ( sK2 = sK2 ),
% 2.19/1.00      inference(instantiation,[status(thm)],[c_1112]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1113,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2029,plain,
% 2.19/1.00      ( X0 != X1 | X0 = k1_xboole_0 | k1_xboole_0 != X1 ),
% 2.19/1.00      inference(instantiation,[status(thm)],[c_1113]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2030,plain,
% 2.19/1.00      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 2.19/1.00      inference(instantiation,[status(thm)],[c_2029]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2332,plain,
% 2.19/1.00      ( r2_hidden(X0,sK1) != iProver_top
% 2.19/1.00      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3)) = iProver_top ),
% 2.19/1.00      inference(global_propositional_subsumption,
% 2.19/1.00                [status(thm)],
% 2.19/1.00                [c_1652,c_331,c_411,c_1141,c_2030]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_3,plain,
% 2.19/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.19/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1664,plain,
% 2.19/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.19/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_5,plain,
% 2.19/1.00      ( m1_subset_1(X0,X1)
% 2.19/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.19/1.00      | ~ r2_hidden(X0,X2) ),
% 2.19/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1662,plain,
% 2.19/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 2.19/1.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.19/1.00      | r2_hidden(X0,X2) != iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2825,plain,
% 2.19/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.19/1.00      | m1_subset_1(X2,X1) = iProver_top
% 2.19/1.00      | r2_hidden(X2,X0) != iProver_top ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_1664,c_1662]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_3354,plain,
% 2.19/1.00      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) != iProver_top
% 2.19/1.00      | m1_subset_1(k1_funct_1(sK3,X1),X0) = iProver_top
% 2.19/1.00      | r2_hidden(X1,sK1) != iProver_top ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_2332,c_2825]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_3731,plain,
% 2.19/1.00      ( m1_subset_1(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
% 2.19/1.00      | r2_hidden(X0,sK1) != iProver_top ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_2553,c_3354]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_3815,plain,
% 2.19/1.00      ( r2_hidden(X0,sK1) != iProver_top
% 2.19/1.00      | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
% 2.19/1.00      | v1_xboole_0(k1_relat_1(sK4)) = iProver_top ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_3731,c_1665]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_6,plain,
% 2.19/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.19/1.00      | ~ r2_hidden(X2,X0)
% 2.19/1.00      | ~ v1_xboole_0(X1) ),
% 2.19/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_161,plain,
% 2.19/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.19/1.00      inference(prop_impl,[status(thm)],[c_3]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_213,plain,
% 2.19/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 2.19/1.00      inference(bin_hyper_res,[status(thm)],[c_6,c_161]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1654,plain,
% 2.19/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.19/1.00      | r2_hidden(X2,X0) != iProver_top
% 2.19/1.00      | v1_xboole_0(X1) != iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_213]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_3223,plain,
% 2.19/1.00      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) != iProver_top
% 2.19/1.00      | r2_hidden(X1,sK1) != iProver_top
% 2.19/1.00      | v1_xboole_0(X0) != iProver_top ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_2332,c_1654]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_3564,plain,
% 2.19/1.00      ( r2_hidden(X0,sK1) != iProver_top
% 2.19/1.00      | v1_xboole_0(k1_relat_1(sK4)) != iProver_top ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_2553,c_3223]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_3571,plain,
% 2.19/1.00      ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_2618,c_3564]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_3970,plain,
% 2.19/1.00      ( r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
% 2.19/1.00      | r2_hidden(X0,sK1) != iProver_top ),
% 2.19/1.00      inference(global_propositional_subsumption,
% 2.19/1.00                [status(thm)],
% 2.19/1.00                [c_3815,c_3571]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_3971,plain,
% 2.19/1.00      ( r2_hidden(X0,sK1) != iProver_top
% 2.19/1.00      | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top ),
% 2.19/1.00      inference(renaming,[status(thm)],[c_3970]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_9,plain,
% 2.19/1.00      ( v5_relat_1(X0,X1)
% 2.19/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.19/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_11,plain,
% 2.19/1.00      ( ~ v5_relat_1(X0,X1)
% 2.19/1.00      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.19/1.00      | ~ v1_funct_1(X0)
% 2.19/1.00      | ~ v1_relat_1(X0)
% 2.19/1.00      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.19/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_298,plain,
% 2.19/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/1.00      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.19/1.00      | ~ v1_funct_1(X0)
% 2.19/1.00      | ~ v1_relat_1(X0)
% 2.19/1.00      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.19/1.00      inference(resolution,[status(thm)],[c_9,c_11]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_19,negated_conjecture,
% 2.19/1.00      ( v1_funct_1(sK4) ),
% 2.19/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_490,plain,
% 2.19/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/1.00      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.19/1.00      | ~ v1_relat_1(X0)
% 2.19/1.00      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3)
% 2.19/1.00      | sK4 != X0 ),
% 2.19/1.00      inference(resolution_lifted,[status(thm)],[c_298,c_19]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_491,plain,
% 2.19/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.19/1.00      | ~ r2_hidden(X2,k1_relat_1(sK4))
% 2.19/1.00      | ~ v1_relat_1(sK4)
% 2.19/1.00      | k7_partfun1(X1,sK4,X2) = k1_funct_1(sK4,X2) ),
% 2.19/1.00      inference(unflattening,[status(thm)],[c_490]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1649,plain,
% 2.19/1.00      ( k7_partfun1(X0,sK4,X1) = k1_funct_1(sK4,X1)
% 2.19/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 2.19/1.00      | r2_hidden(X1,k1_relat_1(sK4)) != iProver_top
% 2.19/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1998,plain,
% 2.19/1.00      ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
% 2.19/1.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.19/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_1657,c_1649]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_29,plain,
% 2.19/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_4,plain,
% 2.19/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.19/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1827,plain,
% 2.19/1.00      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK0))
% 2.19/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 2.19/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1828,plain,
% 2.19/1.00      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK0)) = iProver_top
% 2.19/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_1827]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_7,plain,
% 2.19/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.19/1.00      | ~ v1_relat_1(X1)
% 2.19/1.00      | v1_relat_1(X0) ),
% 2.19/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_214,plain,
% 2.19/1.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.19/1.00      inference(bin_hyper_res,[status(thm)],[c_7,c_161]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1833,plain,
% 2.19/1.00      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 2.19/1.00      | v1_relat_1(X0)
% 2.19/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.19/1.00      inference(instantiation,[status(thm)],[c_214]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2137,plain,
% 2.19/1.00      ( ~ r1_tarski(sK4,k2_zfmisc_1(sK2,sK0))
% 2.19/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
% 2.19/1.00      | v1_relat_1(sK4) ),
% 2.19/1.00      inference(instantiation,[status(thm)],[c_1833]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2138,plain,
% 2.19/1.00      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK0)) != iProver_top
% 2.19/1.00      | v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top
% 2.19/1.00      | v1_relat_1(sK4) = iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_2137]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_8,plain,
% 2.19/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.19/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2187,plain,
% 2.19/1.00      ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
% 2.19/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2188,plain,
% 2.19/1.00      ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) = iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_2187]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2197,plain,
% 2.19/1.00      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.19/1.00      | k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0) ),
% 2.19/1.00      inference(global_propositional_subsumption,
% 2.19/1.00                [status(thm)],
% 2.19/1.00                [c_1998,c_29,c_1828,c_2138,c_2188]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2198,plain,
% 2.19/1.00      ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
% 2.19/1.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.19/1.00      inference(renaming,[status(thm)],[c_2197]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_3980,plain,
% 2.19/1.00      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.19/1.00      | r2_hidden(X0,sK1) != iProver_top ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_3971,c_2198]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_4227,plain,
% 2.19/1.00      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_2618,c_3980]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_12,plain,
% 2.19/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/1.00      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 2.19/1.00      | ~ m1_subset_1(X5,X1)
% 2.19/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.19/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/1.00      | ~ v1_funct_1(X4)
% 2.19/1.00      | ~ v1_funct_1(X0)
% 2.19/1.00      | v1_xboole_0(X2)
% 2.19/1.00      | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k1_funct_1(X4,k1_funct_1(X0,X5))
% 2.19/1.00      | k1_xboole_0 = X1 ),
% 2.19/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_345,plain,
% 2.19/1.00      ( ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,X4))
% 2.19/1.00      | ~ m1_subset_1(X5,X0)
% 2.19/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.19/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.19/1.00      | ~ v1_funct_1(X2)
% 2.19/1.00      | ~ v1_funct_1(X4)
% 2.19/1.00      | v1_xboole_0(X1)
% 2.19/1.00      | k1_funct_1(k8_funct_2(X0,X1,X3,X2,X4),X5) = k1_funct_1(X4,k1_funct_1(X2,X5))
% 2.19/1.00      | sK2 != X1
% 2.19/1.00      | sK1 != X0
% 2.19/1.00      | sK3 != X2
% 2.19/1.00      | k1_xboole_0 = X0 ),
% 2.19/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_346,plain,
% 2.19/1.00      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 2.19/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 2.19/1.00      | ~ m1_subset_1(X2,sK1)
% 2.19/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.19/1.00      | ~ v1_funct_1(X1)
% 2.19/1.00      | ~ v1_funct_1(sK3)
% 2.19/1.00      | v1_xboole_0(sK2)
% 2.19/1.00      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.19/1.00      | k1_xboole_0 = sK1 ),
% 2.19/1.00      inference(unflattening,[status(thm)],[c_345]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_350,plain,
% 2.19/1.00      ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.19/1.00      | ~ v1_funct_1(X1)
% 2.19/1.00      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 2.19/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 2.19/1.00      | ~ m1_subset_1(X2,sK1) ),
% 2.19/1.00      inference(global_propositional_subsumption,
% 2.19/1.00                [status(thm)],
% 2.19/1.00                [c_346,c_23,c_22,c_20,c_15]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_351,plain,
% 2.19/1.00      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 2.19/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 2.19/1.00      | ~ m1_subset_1(X2,sK1)
% 2.19/1.00      | ~ v1_funct_1(X1)
% 2.19/1.00      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) ),
% 2.19/1.00      inference(renaming,[status(thm)],[c_350]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_454,plain,
% 2.19/1.00      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 2.19/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 2.19/1.00      | ~ m1_subset_1(X2,sK1)
% 2.19/1.00      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.19/1.00      | sK4 != X1 ),
% 2.19/1.00      inference(resolution_lifted,[status(thm)],[c_351,c_19]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_455,plain,
% 2.19/1.00      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,sK4))
% 2.19/1.00      | ~ m1_subset_1(X1,sK1)
% 2.19/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 2.19/1.00      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,sK4),X1) = k1_funct_1(sK4,k1_funct_1(sK3,X1)) ),
% 2.19/1.00      inference(unflattening,[status(thm)],[c_454]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1651,plain,
% 2.19/1.00      ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,sK4),X1) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
% 2.19/1.00      | r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,sK4)) != iProver_top
% 2.19/1.00      | m1_subset_1(X1,sK1) != iProver_top
% 2.19/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2259,plain,
% 2.19/1.00      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.19/1.00      | m1_subset_1(X0,sK1) != iProver_top
% 2.19/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_1659,c_1651]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2264,plain,
% 2.19/1.00      ( m1_subset_1(X0,sK1) != iProver_top
% 2.19/1.00      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ),
% 2.19/1.00      inference(global_propositional_subsumption,
% 2.19/1.00                [status(thm)],
% 2.19/1.00                [c_2259,c_29]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2265,plain,
% 2.19/1.00      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.19/1.00      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.19/1.00      inference(renaming,[status(thm)],[c_2264]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2272,plain,
% 2.19/1.00      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_1658,c_2265]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_14,negated_conjecture,
% 2.19/1.00      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
% 2.19/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_2330,plain,
% 2.19/1.00      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.19/1.00      inference(demodulation,[status(thm)],[c_2272,c_14]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(contradiction,plain,
% 2.19/1.00      ( $false ),
% 2.19/1.00      inference(minisat,[status(thm)],[c_4227,c_2330]) ).
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.19/1.00  
% 2.19/1.00  ------                               Statistics
% 2.19/1.00  
% 2.19/1.00  ------ General
% 2.19/1.00  
% 2.19/1.00  abstr_ref_over_cycles:                  0
% 2.19/1.00  abstr_ref_under_cycles:                 0
% 2.19/1.00  gc_basic_clause_elim:                   0
% 2.19/1.00  forced_gc_time:                         0
% 2.19/1.00  parsing_time:                           0.01
% 2.19/1.00  unif_index_cands_time:                  0.
% 2.19/1.00  unif_index_add_time:                    0.
% 2.19/1.00  orderings_time:                         0.
% 2.19/1.00  out_proof_time:                         0.011
% 2.19/1.00  total_time:                             0.149
% 2.19/1.00  num_of_symbols:                         54
% 2.19/1.00  num_of_terms:                           2811
% 2.19/1.00  
% 2.19/1.00  ------ Preprocessing
% 2.19/1.00  
% 2.19/1.00  num_of_splits:                          0
% 2.19/1.00  num_of_split_atoms:                     0
% 2.19/1.00  num_of_reused_defs:                     0
% 2.19/1.00  num_eq_ax_congr_red:                    3
% 2.19/1.00  num_of_sem_filtered_clauses:            1
% 2.19/1.00  num_of_subtypes:                        0
% 2.19/1.00  monotx_restored_types:                  0
% 2.19/1.00  sat_num_of_epr_types:                   0
% 2.19/1.00  sat_num_of_non_cyclic_types:            0
% 2.19/1.00  sat_guarded_non_collapsed_types:        0
% 2.19/1.00  num_pure_diseq_elim:                    0
% 2.19/1.00  simp_replaced_by:                       0
% 2.19/1.00  res_preprocessed:                       121
% 2.19/1.00  prep_upred:                             0
% 2.19/1.00  prep_unflattend:                        38
% 2.19/1.00  smt_new_axioms:                         0
% 2.19/1.00  pred_elim_cands:                        5
% 2.19/1.00  pred_elim:                              3
% 2.19/1.00  pred_elim_cl:                           2
% 2.19/1.00  pred_elim_cycles:                       7
% 2.19/1.00  merged_defs:                            8
% 2.19/1.00  merged_defs_ncl:                        0
% 2.19/1.00  bin_hyper_res:                          10
% 2.19/1.00  prep_cycles:                            4
% 2.19/1.00  pred_elim_time:                         0.013
% 2.19/1.00  splitting_time:                         0.
% 2.19/1.00  sem_filter_time:                        0.
% 2.19/1.00  monotx_time:                            0.001
% 2.19/1.00  subtype_inf_time:                       0.
% 2.19/1.00  
% 2.19/1.00  ------ Problem properties
% 2.19/1.00  
% 2.19/1.00  clauses:                                22
% 2.19/1.00  conjectures:                            7
% 2.19/1.00  epr:                                    8
% 2.19/1.00  horn:                                   20
% 2.19/1.00  ground:                                 8
% 2.19/1.00  unary:                                  9
% 2.19/1.00  binary:                                 4
% 2.19/1.00  lits:                                   48
% 2.19/1.00  lits_eq:                                9
% 2.19/1.00  fd_pure:                                0
% 2.19/1.00  fd_pseudo:                              0
% 2.19/1.00  fd_cond:                                1
% 2.19/1.00  fd_pseudo_cond:                         0
% 2.19/1.00  ac_symbols:                             0
% 2.19/1.00  
% 2.19/1.00  ------ Propositional Solver
% 2.19/1.00  
% 2.19/1.00  prop_solver_calls:                      30
% 2.19/1.00  prop_fast_solver_calls:                 891
% 2.19/1.00  smt_solver_calls:                       0
% 2.19/1.00  smt_fast_solver_calls:                  0
% 2.19/1.00  prop_num_of_clauses:                    1112
% 2.19/1.00  prop_preprocess_simplified:             4475
% 2.19/1.00  prop_fo_subsumed:                       15
% 2.19/1.00  prop_solver_time:                       0.
% 2.19/1.00  smt_solver_time:                        0.
% 2.19/1.00  smt_fast_solver_time:                   0.
% 2.19/1.00  prop_fast_solver_time:                  0.
% 2.19/1.00  prop_unsat_core_time:                   0.
% 2.19/1.00  
% 2.19/1.00  ------ QBF
% 2.19/1.00  
% 2.19/1.00  qbf_q_res:                              0
% 2.19/1.00  qbf_num_tautologies:                    0
% 2.19/1.00  qbf_prep_cycles:                        0
% 2.19/1.00  
% 2.19/1.00  ------ BMC1
% 2.19/1.00  
% 2.19/1.00  bmc1_current_bound:                     -1
% 2.19/1.00  bmc1_last_solved_bound:                 -1
% 2.19/1.00  bmc1_unsat_core_size:                   -1
% 2.19/1.00  bmc1_unsat_core_parents_size:           -1
% 2.19/1.00  bmc1_merge_next_fun:                    0
% 2.19/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.19/1.00  
% 2.19/1.00  ------ Instantiation
% 2.19/1.00  
% 2.19/1.00  inst_num_of_clauses:                    394
% 2.19/1.00  inst_num_in_passive:                    0
% 2.19/1.00  inst_num_in_active:                     312
% 2.19/1.00  inst_num_in_unprocessed:                82
% 2.19/1.00  inst_num_of_loops:                      330
% 2.19/1.00  inst_num_of_learning_restarts:          0
% 2.19/1.00  inst_num_moves_active_passive:          12
% 2.19/1.00  inst_lit_activity:                      0
% 2.19/1.00  inst_lit_activity_moves:                0
% 2.19/1.00  inst_num_tautologies:                   0
% 2.19/1.00  inst_num_prop_implied:                  0
% 2.19/1.00  inst_num_existing_simplified:           0
% 2.19/1.00  inst_num_eq_res_simplified:             0
% 2.19/1.00  inst_num_child_elim:                    0
% 2.19/1.00  inst_num_of_dismatching_blockings:      90
% 2.19/1.00  inst_num_of_non_proper_insts:           520
% 2.19/1.00  inst_num_of_duplicates:                 0
% 2.19/1.00  inst_inst_num_from_inst_to_res:         0
% 2.19/1.00  inst_dismatching_checking_time:         0.
% 2.19/1.00  
% 2.19/1.00  ------ Resolution
% 2.19/1.00  
% 2.19/1.00  res_num_of_clauses:                     0
% 2.19/1.00  res_num_in_passive:                     0
% 2.19/1.00  res_num_in_active:                      0
% 2.19/1.00  res_num_of_loops:                       125
% 2.19/1.00  res_forward_subset_subsumed:            140
% 2.19/1.00  res_backward_subset_subsumed:           0
% 2.19/1.00  res_forward_subsumed:                   0
% 2.19/1.00  res_backward_subsumed:                  0
% 2.19/1.00  res_forward_subsumption_resolution:     0
% 2.19/1.00  res_backward_subsumption_resolution:    0
% 2.19/1.00  res_clause_to_clause_subsumption:       161
% 2.19/1.00  res_orphan_elimination:                 0
% 2.19/1.00  res_tautology_del:                      131
% 2.19/1.00  res_num_eq_res_simplified:              0
% 2.19/1.00  res_num_sel_changes:                    0
% 2.19/1.00  res_moves_from_active_to_pass:          0
% 2.19/1.00  
% 2.19/1.00  ------ Superposition
% 2.19/1.00  
% 2.19/1.00  sup_time_total:                         0.
% 2.19/1.00  sup_time_generating:                    0.
% 2.19/1.00  sup_time_sim_full:                      0.
% 2.19/1.00  sup_time_sim_immed:                     0.
% 2.19/1.00  
% 2.19/1.00  sup_num_of_clauses:                     73
% 2.19/1.00  sup_num_in_active:                      62
% 2.19/1.00  sup_num_in_passive:                     11
% 2.19/1.00  sup_num_of_loops:                       64
% 2.19/1.00  sup_fw_superposition:                   41
% 2.19/1.00  sup_bw_superposition:                   16
% 2.19/1.00  sup_immediate_simplified:               1
% 2.19/1.00  sup_given_eliminated:                   0
% 2.19/1.00  comparisons_done:                       0
% 2.19/1.00  comparisons_avoided:                    0
% 2.19/1.00  
% 2.19/1.00  ------ Simplifications
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  sim_fw_subset_subsumed:                 0
% 2.19/1.00  sim_bw_subset_subsumed:                 1
% 2.19/1.00  sim_fw_subsumed:                        1
% 2.19/1.00  sim_bw_subsumed:                        0
% 2.19/1.00  sim_fw_subsumption_res:                 0
% 2.19/1.00  sim_bw_subsumption_res:                 0
% 2.19/1.00  sim_tautology_del:                      1
% 2.19/1.00  sim_eq_tautology_del:                   1
% 2.19/1.00  sim_eq_res_simp:                        0
% 2.19/1.00  sim_fw_demodulated:                     0
% 2.19/1.00  sim_bw_demodulated:                     2
% 2.19/1.00  sim_light_normalised:                   0
% 2.19/1.00  sim_joinable_taut:                      0
% 2.19/1.00  sim_joinable_simp:                      0
% 2.19/1.00  sim_ac_normalised:                      0
% 2.19/1.00  sim_smt_subsumption:                    0
% 2.19/1.00  
%------------------------------------------------------------------------------

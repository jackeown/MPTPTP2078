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
% DateTime   : Thu Dec  3 12:09:54 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 432 expanded)
%              Number of clauses        :   84 ( 118 expanded)
%              Number of leaves         :   20 ( 145 expanded)
%              Depth                    :   18
%              Number of atoms          :  533 (3216 expanded)
%              Number of equality atoms :  207 ( 850 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f37,f45,f44,f43,f42])).

fof(f73,plain,(
    m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f39])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f67,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2054,plain,
    ( m1_subset_1(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2066,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2882,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2054,c_2066])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_10,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2263,plain,
    ( r2_hidden(sK0(sK2),sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2264,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(sK0(sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2263])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2379,plain,
    ( ~ r2_hidden(sK0(sK2),sK2)
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2380,plain,
    ( r2_hidden(sK0(sK2),sK2) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2379])).

cnf(c_3588,plain,
    ( r2_hidden(sK6,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2882,c_21,c_2264,c_2380])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2053,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2061,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2780,plain,
    ( v5_relat_1(sK5,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2053,c_2061])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2051,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2059,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2792,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2051,c_2059])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2055,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3015,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2792,c_2055])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2060,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2872,plain,
    ( k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2053,c_2060])).

cnf(c_3157,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3015,c_2872])).

cnf(c_4,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2064,plain,
    ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v5_relat_1(X0,X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3345,plain,
    ( v5_relat_1(sK4,k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3157,c_2064])).

cnf(c_33,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2266,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2411,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2266])).

cnf(c_2412,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2411])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2432,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2433,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2432])).

cnf(c_3913,plain,
    ( v5_relat_1(sK4,k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3345,c_33,c_2412,c_2433])).

cnf(c_19,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2056,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2057,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | v5_relat_1(X1,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3449,plain,
    ( k7_partfun1(X0,X1,k1_funct_1(X2,X3)) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | v5_relat_1(X1,X0) != iProver_top
    | v5_relat_1(X2,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X3,k1_relat_1(X2)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2056,c_2057])).

cnf(c_5359,plain,
    ( k7_partfun1(X0,sK5,k1_funct_1(sK4,X1)) = k1_funct_1(sK5,k1_funct_1(sK4,X1))
    | v5_relat_1(sK5,X0) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3913,c_3449])).

cnf(c_2873,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2051,c_2060])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_759,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X2
    | sK2 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_760,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_759])).

cnf(c_762,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_760,c_26])).

cnf(c_3083,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2873,c_762])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_333,plain,
    ( sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_29])).

cnf(c_3160,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3083,c_333])).

cnf(c_5384,plain,
    ( k7_partfun1(X0,sK5,k1_funct_1(sK4,X1)) = k1_funct_1(sK5,k1_funct_1(sK4,X1))
    | v5_relat_1(sK5,X0) != iProver_top
    | r2_hidden(X1,sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5359,c_3160])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_34,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_35,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2408,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2266])).

cnf(c_2409,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2408])).

cnf(c_2429,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2430,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2429])).

cnf(c_6395,plain,
    ( k7_partfun1(X0,sK5,k1_funct_1(sK4,X1)) = k1_funct_1(sK5,k1_funct_1(sK4,X1))
    | v5_relat_1(sK5,X0) != iProver_top
    | r2_hidden(X1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5384,c_31,c_33,c_34,c_35,c_2409,c_2412,c_2430,c_2433])).

cnf(c_6404,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,X0)) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2780,c_6395])).

cnf(c_6413,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(superposition,[status(thm)],[c_3588,c_6404])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f65])).

cnf(c_732,plain,
    ( ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,X4))
    | ~ m1_subset_1(X5,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | k1_funct_1(k8_funct_2(X0,X1,X3,X2,X4),X5) = k1_funct_1(X4,k1_funct_1(X2,X5))
    | sK3 != X1
    | sK2 != X0
    | sK4 != X2
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_733,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
    | ~ m1_subset_1(X2,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK3)
    | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_737,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
    | ~ m1_subset_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_733,c_29,c_28,c_26,c_21])).

cnf(c_738,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
    | ~ m1_subset_1(X2,sK2)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2)) ),
    inference(renaming,[status(thm)],[c_737])).

cnf(c_2046,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
    | m1_subset_1(X2,sK2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_2574,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2055,c_2046])).

cnf(c_2636,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2574,c_34,c_35])).

cnf(c_2644,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(superposition,[status(thm)],[c_2054,c_2636])).

cnf(c_20,negated_conjecture,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2646,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(demodulation,[status(thm)],[c_2644,c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6413,c_2646])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 19:33:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  % Running in FOF mode
% 2.93/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.03  
% 2.93/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.93/1.03  
% 2.93/1.03  ------  iProver source info
% 2.93/1.03  
% 2.93/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.93/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.93/1.03  git: non_committed_changes: false
% 2.93/1.03  git: last_make_outside_of_git: false
% 2.93/1.03  
% 2.93/1.03  ------ 
% 2.93/1.03  
% 2.93/1.03  ------ Input Options
% 2.93/1.03  
% 2.93/1.03  --out_options                           all
% 2.93/1.03  --tptp_safe_out                         true
% 2.93/1.03  --problem_path                          ""
% 2.93/1.03  --include_path                          ""
% 2.93/1.03  --clausifier                            res/vclausify_rel
% 2.93/1.03  --clausifier_options                    --mode clausify
% 2.93/1.03  --stdin                                 false
% 2.93/1.03  --stats_out                             all
% 2.93/1.03  
% 2.93/1.03  ------ General Options
% 2.93/1.03  
% 2.93/1.03  --fof                                   false
% 2.93/1.03  --time_out_real                         305.
% 2.93/1.03  --time_out_virtual                      -1.
% 2.93/1.03  --symbol_type_check                     false
% 2.93/1.03  --clausify_out                          false
% 2.93/1.03  --sig_cnt_out                           false
% 2.93/1.03  --trig_cnt_out                          false
% 2.93/1.03  --trig_cnt_out_tolerance                1.
% 2.93/1.03  --trig_cnt_out_sk_spl                   false
% 2.93/1.03  --abstr_cl_out                          false
% 2.93/1.03  
% 2.93/1.03  ------ Global Options
% 2.93/1.03  
% 2.93/1.03  --schedule                              default
% 2.93/1.03  --add_important_lit                     false
% 2.93/1.03  --prop_solver_per_cl                    1000
% 2.93/1.03  --min_unsat_core                        false
% 2.93/1.03  --soft_assumptions                      false
% 2.93/1.03  --soft_lemma_size                       3
% 2.93/1.03  --prop_impl_unit_size                   0
% 2.93/1.03  --prop_impl_unit                        []
% 2.93/1.03  --share_sel_clauses                     true
% 2.93/1.03  --reset_solvers                         false
% 2.93/1.03  --bc_imp_inh                            [conj_cone]
% 2.93/1.03  --conj_cone_tolerance                   3.
% 2.93/1.03  --extra_neg_conj                        none
% 2.93/1.03  --large_theory_mode                     true
% 2.93/1.03  --prolific_symb_bound                   200
% 2.93/1.03  --lt_threshold                          2000
% 2.93/1.03  --clause_weak_htbl                      true
% 2.93/1.03  --gc_record_bc_elim                     false
% 2.93/1.03  
% 2.93/1.03  ------ Preprocessing Options
% 2.93/1.03  
% 2.93/1.03  --preprocessing_flag                    true
% 2.93/1.03  --time_out_prep_mult                    0.1
% 2.93/1.03  --splitting_mode                        input
% 2.93/1.03  --splitting_grd                         true
% 2.93/1.03  --splitting_cvd                         false
% 2.93/1.03  --splitting_cvd_svl                     false
% 2.93/1.03  --splitting_nvd                         32
% 2.93/1.03  --sub_typing                            true
% 2.93/1.03  --prep_gs_sim                           true
% 2.93/1.03  --prep_unflatten                        true
% 2.93/1.03  --prep_res_sim                          true
% 2.93/1.03  --prep_upred                            true
% 2.93/1.03  --prep_sem_filter                       exhaustive
% 2.93/1.03  --prep_sem_filter_out                   false
% 2.93/1.03  --pred_elim                             true
% 2.93/1.03  --res_sim_input                         true
% 2.93/1.03  --eq_ax_congr_red                       true
% 2.93/1.03  --pure_diseq_elim                       true
% 2.93/1.03  --brand_transform                       false
% 2.93/1.03  --non_eq_to_eq                          false
% 2.93/1.03  --prep_def_merge                        true
% 2.93/1.03  --prep_def_merge_prop_impl              false
% 2.93/1.03  --prep_def_merge_mbd                    true
% 2.93/1.03  --prep_def_merge_tr_red                 false
% 2.93/1.03  --prep_def_merge_tr_cl                  false
% 2.93/1.03  --smt_preprocessing                     true
% 2.93/1.03  --smt_ac_axioms                         fast
% 2.93/1.03  --preprocessed_out                      false
% 2.93/1.03  --preprocessed_stats                    false
% 2.93/1.03  
% 2.93/1.03  ------ Abstraction refinement Options
% 2.93/1.03  
% 2.93/1.03  --abstr_ref                             []
% 2.93/1.03  --abstr_ref_prep                        false
% 2.93/1.03  --abstr_ref_until_sat                   false
% 2.93/1.03  --abstr_ref_sig_restrict                funpre
% 2.93/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.93/1.03  --abstr_ref_under                       []
% 2.93/1.03  
% 2.93/1.03  ------ SAT Options
% 2.93/1.03  
% 2.93/1.03  --sat_mode                              false
% 2.93/1.03  --sat_fm_restart_options                ""
% 2.93/1.03  --sat_gr_def                            false
% 2.93/1.03  --sat_epr_types                         true
% 2.93/1.03  --sat_non_cyclic_types                  false
% 2.93/1.03  --sat_finite_models                     false
% 2.93/1.03  --sat_fm_lemmas                         false
% 2.93/1.03  --sat_fm_prep                           false
% 2.93/1.03  --sat_fm_uc_incr                        true
% 2.93/1.03  --sat_out_model                         small
% 2.93/1.03  --sat_out_clauses                       false
% 2.93/1.03  
% 2.93/1.03  ------ QBF Options
% 2.93/1.03  
% 2.93/1.03  --qbf_mode                              false
% 2.93/1.03  --qbf_elim_univ                         false
% 2.93/1.03  --qbf_dom_inst                          none
% 2.93/1.03  --qbf_dom_pre_inst                      false
% 2.93/1.03  --qbf_sk_in                             false
% 2.93/1.03  --qbf_pred_elim                         true
% 2.93/1.03  --qbf_split                             512
% 2.93/1.03  
% 2.93/1.03  ------ BMC1 Options
% 2.93/1.03  
% 2.93/1.03  --bmc1_incremental                      false
% 2.93/1.03  --bmc1_axioms                           reachable_all
% 2.93/1.03  --bmc1_min_bound                        0
% 2.93/1.03  --bmc1_max_bound                        -1
% 2.93/1.03  --bmc1_max_bound_default                -1
% 2.93/1.03  --bmc1_symbol_reachability              true
% 2.93/1.03  --bmc1_property_lemmas                  false
% 2.93/1.03  --bmc1_k_induction                      false
% 2.93/1.03  --bmc1_non_equiv_states                 false
% 2.93/1.03  --bmc1_deadlock                         false
% 2.93/1.03  --bmc1_ucm                              false
% 2.93/1.03  --bmc1_add_unsat_core                   none
% 2.93/1.03  --bmc1_unsat_core_children              false
% 2.93/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.93/1.03  --bmc1_out_stat                         full
% 2.93/1.03  --bmc1_ground_init                      false
% 2.93/1.03  --bmc1_pre_inst_next_state              false
% 2.93/1.03  --bmc1_pre_inst_state                   false
% 2.93/1.03  --bmc1_pre_inst_reach_state             false
% 2.93/1.03  --bmc1_out_unsat_core                   false
% 2.93/1.03  --bmc1_aig_witness_out                  false
% 2.93/1.03  --bmc1_verbose                          false
% 2.93/1.03  --bmc1_dump_clauses_tptp                false
% 2.93/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.93/1.03  --bmc1_dump_file                        -
% 2.93/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.93/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.93/1.03  --bmc1_ucm_extend_mode                  1
% 2.93/1.03  --bmc1_ucm_init_mode                    2
% 2.93/1.03  --bmc1_ucm_cone_mode                    none
% 2.93/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.93/1.03  --bmc1_ucm_relax_model                  4
% 2.93/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.93/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.93/1.03  --bmc1_ucm_layered_model                none
% 2.93/1.03  --bmc1_ucm_max_lemma_size               10
% 2.93/1.03  
% 2.93/1.03  ------ AIG Options
% 2.93/1.03  
% 2.93/1.03  --aig_mode                              false
% 2.93/1.03  
% 2.93/1.03  ------ Instantiation Options
% 2.93/1.03  
% 2.93/1.03  --instantiation_flag                    true
% 2.93/1.03  --inst_sos_flag                         false
% 2.93/1.03  --inst_sos_phase                        true
% 2.93/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.93/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.93/1.03  --inst_lit_sel_side                     num_symb
% 2.93/1.03  --inst_solver_per_active                1400
% 2.93/1.03  --inst_solver_calls_frac                1.
% 2.93/1.03  --inst_passive_queue_type               priority_queues
% 2.93/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.93/1.03  --inst_passive_queues_freq              [25;2]
% 2.93/1.03  --inst_dismatching                      true
% 2.93/1.03  --inst_eager_unprocessed_to_passive     true
% 2.93/1.03  --inst_prop_sim_given                   true
% 2.93/1.03  --inst_prop_sim_new                     false
% 2.93/1.03  --inst_subs_new                         false
% 2.93/1.03  --inst_eq_res_simp                      false
% 2.93/1.03  --inst_subs_given                       false
% 2.93/1.03  --inst_orphan_elimination               true
% 2.93/1.03  --inst_learning_loop_flag               true
% 2.93/1.03  --inst_learning_start                   3000
% 2.93/1.03  --inst_learning_factor                  2
% 2.93/1.03  --inst_start_prop_sim_after_learn       3
% 2.93/1.03  --inst_sel_renew                        solver
% 2.93/1.03  --inst_lit_activity_flag                true
% 2.93/1.03  --inst_restr_to_given                   false
% 2.93/1.03  --inst_activity_threshold               500
% 2.93/1.03  --inst_out_proof                        true
% 2.93/1.03  
% 2.93/1.03  ------ Resolution Options
% 2.93/1.03  
% 2.93/1.03  --resolution_flag                       true
% 2.93/1.03  --res_lit_sel                           adaptive
% 2.93/1.03  --res_lit_sel_side                      none
% 2.93/1.03  --res_ordering                          kbo
% 2.93/1.03  --res_to_prop_solver                    active
% 2.93/1.03  --res_prop_simpl_new                    false
% 2.93/1.03  --res_prop_simpl_given                  true
% 2.93/1.03  --res_passive_queue_type                priority_queues
% 2.93/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.93/1.03  --res_passive_queues_freq               [15;5]
% 2.93/1.03  --res_forward_subs                      full
% 2.93/1.03  --res_backward_subs                     full
% 2.93/1.03  --res_forward_subs_resolution           true
% 2.93/1.03  --res_backward_subs_resolution          true
% 2.93/1.03  --res_orphan_elimination                true
% 2.93/1.03  --res_time_limit                        2.
% 2.93/1.03  --res_out_proof                         true
% 2.93/1.03  
% 2.93/1.03  ------ Superposition Options
% 2.93/1.03  
% 2.93/1.03  --superposition_flag                    true
% 2.93/1.03  --sup_passive_queue_type                priority_queues
% 2.93/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.93/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.93/1.03  --demod_completeness_check              fast
% 2.93/1.03  --demod_use_ground                      true
% 2.93/1.03  --sup_to_prop_solver                    passive
% 2.93/1.03  --sup_prop_simpl_new                    true
% 2.93/1.03  --sup_prop_simpl_given                  true
% 2.93/1.03  --sup_fun_splitting                     false
% 2.93/1.03  --sup_smt_interval                      50000
% 2.93/1.03  
% 2.93/1.03  ------ Superposition Simplification Setup
% 2.93/1.03  
% 2.93/1.03  --sup_indices_passive                   []
% 2.93/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.93/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.03  --sup_full_bw                           [BwDemod]
% 2.93/1.03  --sup_immed_triv                        [TrivRules]
% 2.93/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.93/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.03  --sup_immed_bw_main                     []
% 2.93/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.93/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/1.03  
% 2.93/1.03  ------ Combination Options
% 2.93/1.03  
% 2.93/1.03  --comb_res_mult                         3
% 2.93/1.03  --comb_sup_mult                         2
% 2.93/1.03  --comb_inst_mult                        10
% 2.93/1.03  
% 2.93/1.03  ------ Debug Options
% 2.93/1.03  
% 2.93/1.03  --dbg_backtrace                         false
% 2.93/1.03  --dbg_dump_prop_clauses                 false
% 2.93/1.03  --dbg_dump_prop_clauses_file            -
% 2.93/1.03  --dbg_out_stat                          false
% 2.93/1.03  ------ Parsing...
% 2.93/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.93/1.03  
% 2.93/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.93/1.03  
% 2.93/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.93/1.03  
% 2.93/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.93/1.03  ------ Proving...
% 2.93/1.03  ------ Problem Properties 
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  clauses                                 27
% 2.93/1.03  conjectures                             9
% 2.93/1.03  EPR                                     9
% 2.93/1.03  Horn                                    23
% 2.93/1.03  unary                                   12
% 2.93/1.03  binary                                  6
% 2.93/1.03  lits                                    65
% 2.93/1.03  lits eq                                 16
% 2.93/1.03  fd_pure                                 0
% 2.93/1.03  fd_pseudo                               0
% 2.93/1.03  fd_cond                                 2
% 2.93/1.03  fd_pseudo_cond                          0
% 2.93/1.03  AC symbols                              0
% 2.93/1.03  
% 2.93/1.03  ------ Schedule dynamic 5 is on 
% 2.93/1.03  
% 2.93/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  ------ 
% 2.93/1.03  Current options:
% 2.93/1.03  ------ 
% 2.93/1.03  
% 2.93/1.03  ------ Input Options
% 2.93/1.03  
% 2.93/1.03  --out_options                           all
% 2.93/1.03  --tptp_safe_out                         true
% 2.93/1.03  --problem_path                          ""
% 2.93/1.03  --include_path                          ""
% 2.93/1.03  --clausifier                            res/vclausify_rel
% 2.93/1.03  --clausifier_options                    --mode clausify
% 2.93/1.03  --stdin                                 false
% 2.93/1.03  --stats_out                             all
% 2.93/1.03  
% 2.93/1.03  ------ General Options
% 2.93/1.03  
% 2.93/1.03  --fof                                   false
% 2.93/1.03  --time_out_real                         305.
% 2.93/1.03  --time_out_virtual                      -1.
% 2.93/1.03  --symbol_type_check                     false
% 2.93/1.03  --clausify_out                          false
% 2.93/1.03  --sig_cnt_out                           false
% 2.93/1.03  --trig_cnt_out                          false
% 2.93/1.03  --trig_cnt_out_tolerance                1.
% 2.93/1.03  --trig_cnt_out_sk_spl                   false
% 2.93/1.03  --abstr_cl_out                          false
% 2.93/1.03  
% 2.93/1.03  ------ Global Options
% 2.93/1.03  
% 2.93/1.03  --schedule                              default
% 2.93/1.03  --add_important_lit                     false
% 2.93/1.03  --prop_solver_per_cl                    1000
% 2.93/1.03  --min_unsat_core                        false
% 2.93/1.03  --soft_assumptions                      false
% 2.93/1.03  --soft_lemma_size                       3
% 2.93/1.03  --prop_impl_unit_size                   0
% 2.93/1.03  --prop_impl_unit                        []
% 2.93/1.03  --share_sel_clauses                     true
% 2.93/1.03  --reset_solvers                         false
% 2.93/1.03  --bc_imp_inh                            [conj_cone]
% 2.93/1.03  --conj_cone_tolerance                   3.
% 2.93/1.03  --extra_neg_conj                        none
% 2.93/1.03  --large_theory_mode                     true
% 2.93/1.03  --prolific_symb_bound                   200
% 2.93/1.03  --lt_threshold                          2000
% 2.93/1.03  --clause_weak_htbl                      true
% 2.93/1.03  --gc_record_bc_elim                     false
% 2.93/1.03  
% 2.93/1.03  ------ Preprocessing Options
% 2.93/1.03  
% 2.93/1.03  --preprocessing_flag                    true
% 2.93/1.03  --time_out_prep_mult                    0.1
% 2.93/1.03  --splitting_mode                        input
% 2.93/1.03  --splitting_grd                         true
% 2.93/1.03  --splitting_cvd                         false
% 2.93/1.03  --splitting_cvd_svl                     false
% 2.93/1.03  --splitting_nvd                         32
% 2.93/1.03  --sub_typing                            true
% 2.93/1.03  --prep_gs_sim                           true
% 2.93/1.03  --prep_unflatten                        true
% 2.93/1.03  --prep_res_sim                          true
% 2.93/1.03  --prep_upred                            true
% 2.93/1.03  --prep_sem_filter                       exhaustive
% 2.93/1.03  --prep_sem_filter_out                   false
% 2.93/1.03  --pred_elim                             true
% 2.93/1.03  --res_sim_input                         true
% 2.93/1.03  --eq_ax_congr_red                       true
% 2.93/1.03  --pure_diseq_elim                       true
% 2.93/1.03  --brand_transform                       false
% 2.93/1.03  --non_eq_to_eq                          false
% 2.93/1.03  --prep_def_merge                        true
% 2.93/1.03  --prep_def_merge_prop_impl              false
% 2.93/1.03  --prep_def_merge_mbd                    true
% 2.93/1.03  --prep_def_merge_tr_red                 false
% 2.93/1.03  --prep_def_merge_tr_cl                  false
% 2.93/1.03  --smt_preprocessing                     true
% 2.93/1.03  --smt_ac_axioms                         fast
% 2.93/1.03  --preprocessed_out                      false
% 2.93/1.03  --preprocessed_stats                    false
% 2.93/1.03  
% 2.93/1.03  ------ Abstraction refinement Options
% 2.93/1.03  
% 2.93/1.03  --abstr_ref                             []
% 2.93/1.03  --abstr_ref_prep                        false
% 2.93/1.03  --abstr_ref_until_sat                   false
% 2.93/1.03  --abstr_ref_sig_restrict                funpre
% 2.93/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.93/1.03  --abstr_ref_under                       []
% 2.93/1.03  
% 2.93/1.03  ------ SAT Options
% 2.93/1.03  
% 2.93/1.03  --sat_mode                              false
% 2.93/1.03  --sat_fm_restart_options                ""
% 2.93/1.03  --sat_gr_def                            false
% 2.93/1.03  --sat_epr_types                         true
% 2.93/1.03  --sat_non_cyclic_types                  false
% 2.93/1.03  --sat_finite_models                     false
% 2.93/1.03  --sat_fm_lemmas                         false
% 2.93/1.03  --sat_fm_prep                           false
% 2.93/1.03  --sat_fm_uc_incr                        true
% 2.93/1.03  --sat_out_model                         small
% 2.93/1.03  --sat_out_clauses                       false
% 2.93/1.03  
% 2.93/1.03  ------ QBF Options
% 2.93/1.03  
% 2.93/1.03  --qbf_mode                              false
% 2.93/1.03  --qbf_elim_univ                         false
% 2.93/1.03  --qbf_dom_inst                          none
% 2.93/1.03  --qbf_dom_pre_inst                      false
% 2.93/1.03  --qbf_sk_in                             false
% 2.93/1.03  --qbf_pred_elim                         true
% 2.93/1.03  --qbf_split                             512
% 2.93/1.03  
% 2.93/1.03  ------ BMC1 Options
% 2.93/1.03  
% 2.93/1.03  --bmc1_incremental                      false
% 2.93/1.03  --bmc1_axioms                           reachable_all
% 2.93/1.03  --bmc1_min_bound                        0
% 2.93/1.03  --bmc1_max_bound                        -1
% 2.93/1.03  --bmc1_max_bound_default                -1
% 2.93/1.03  --bmc1_symbol_reachability              true
% 2.93/1.03  --bmc1_property_lemmas                  false
% 2.93/1.03  --bmc1_k_induction                      false
% 2.93/1.03  --bmc1_non_equiv_states                 false
% 2.93/1.03  --bmc1_deadlock                         false
% 2.93/1.03  --bmc1_ucm                              false
% 2.93/1.03  --bmc1_add_unsat_core                   none
% 2.93/1.03  --bmc1_unsat_core_children              false
% 2.93/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.93/1.03  --bmc1_out_stat                         full
% 2.93/1.03  --bmc1_ground_init                      false
% 2.93/1.03  --bmc1_pre_inst_next_state              false
% 2.93/1.03  --bmc1_pre_inst_state                   false
% 2.93/1.03  --bmc1_pre_inst_reach_state             false
% 2.93/1.03  --bmc1_out_unsat_core                   false
% 2.93/1.03  --bmc1_aig_witness_out                  false
% 2.93/1.03  --bmc1_verbose                          false
% 2.93/1.03  --bmc1_dump_clauses_tptp                false
% 2.93/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.93/1.03  --bmc1_dump_file                        -
% 2.93/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.93/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.93/1.03  --bmc1_ucm_extend_mode                  1
% 2.93/1.03  --bmc1_ucm_init_mode                    2
% 2.93/1.03  --bmc1_ucm_cone_mode                    none
% 2.93/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.93/1.03  --bmc1_ucm_relax_model                  4
% 2.93/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.93/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.93/1.03  --bmc1_ucm_layered_model                none
% 2.93/1.03  --bmc1_ucm_max_lemma_size               10
% 2.93/1.03  
% 2.93/1.03  ------ AIG Options
% 2.93/1.03  
% 2.93/1.03  --aig_mode                              false
% 2.93/1.03  
% 2.93/1.03  ------ Instantiation Options
% 2.93/1.03  
% 2.93/1.03  --instantiation_flag                    true
% 2.93/1.03  --inst_sos_flag                         false
% 2.93/1.03  --inst_sos_phase                        true
% 2.93/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.93/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.93/1.03  --inst_lit_sel_side                     none
% 2.93/1.03  --inst_solver_per_active                1400
% 2.93/1.03  --inst_solver_calls_frac                1.
% 2.93/1.03  --inst_passive_queue_type               priority_queues
% 2.93/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.93/1.03  --inst_passive_queues_freq              [25;2]
% 2.93/1.03  --inst_dismatching                      true
% 2.93/1.03  --inst_eager_unprocessed_to_passive     true
% 2.93/1.03  --inst_prop_sim_given                   true
% 2.93/1.03  --inst_prop_sim_new                     false
% 2.93/1.03  --inst_subs_new                         false
% 2.93/1.03  --inst_eq_res_simp                      false
% 2.93/1.03  --inst_subs_given                       false
% 2.93/1.03  --inst_orphan_elimination               true
% 2.93/1.03  --inst_learning_loop_flag               true
% 2.93/1.03  --inst_learning_start                   3000
% 2.93/1.03  --inst_learning_factor                  2
% 2.93/1.03  --inst_start_prop_sim_after_learn       3
% 2.93/1.03  --inst_sel_renew                        solver
% 2.93/1.03  --inst_lit_activity_flag                true
% 2.93/1.03  --inst_restr_to_given                   false
% 2.93/1.03  --inst_activity_threshold               500
% 2.93/1.03  --inst_out_proof                        true
% 2.93/1.03  
% 2.93/1.03  ------ Resolution Options
% 2.93/1.03  
% 2.93/1.03  --resolution_flag                       false
% 2.93/1.03  --res_lit_sel                           adaptive
% 2.93/1.03  --res_lit_sel_side                      none
% 2.93/1.03  --res_ordering                          kbo
% 2.93/1.03  --res_to_prop_solver                    active
% 2.93/1.03  --res_prop_simpl_new                    false
% 2.93/1.03  --res_prop_simpl_given                  true
% 2.93/1.03  --res_passive_queue_type                priority_queues
% 2.93/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.93/1.03  --res_passive_queues_freq               [15;5]
% 2.93/1.03  --res_forward_subs                      full
% 2.93/1.03  --res_backward_subs                     full
% 2.93/1.03  --res_forward_subs_resolution           true
% 2.93/1.03  --res_backward_subs_resolution          true
% 2.93/1.03  --res_orphan_elimination                true
% 2.93/1.03  --res_time_limit                        2.
% 2.93/1.03  --res_out_proof                         true
% 2.93/1.03  
% 2.93/1.03  ------ Superposition Options
% 2.93/1.03  
% 2.93/1.03  --superposition_flag                    true
% 2.93/1.03  --sup_passive_queue_type                priority_queues
% 2.93/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.93/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.93/1.03  --demod_completeness_check              fast
% 2.93/1.03  --demod_use_ground                      true
% 2.93/1.03  --sup_to_prop_solver                    passive
% 2.93/1.03  --sup_prop_simpl_new                    true
% 2.93/1.03  --sup_prop_simpl_given                  true
% 2.93/1.03  --sup_fun_splitting                     false
% 2.93/1.03  --sup_smt_interval                      50000
% 2.93/1.03  
% 2.93/1.03  ------ Superposition Simplification Setup
% 2.93/1.03  
% 2.93/1.03  --sup_indices_passive                   []
% 2.93/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.93/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.03  --sup_full_bw                           [BwDemod]
% 2.93/1.03  --sup_immed_triv                        [TrivRules]
% 2.93/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.93/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.03  --sup_immed_bw_main                     []
% 2.93/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.93/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/1.03  
% 2.93/1.03  ------ Combination Options
% 2.93/1.03  
% 2.93/1.03  --comb_res_mult                         3
% 2.93/1.03  --comb_sup_mult                         2
% 2.93/1.03  --comb_inst_mult                        10
% 2.93/1.03  
% 2.93/1.03  ------ Debug Options
% 2.93/1.03  
% 2.93/1.03  --dbg_backtrace                         false
% 2.93/1.03  --dbg_dump_prop_clauses                 false
% 2.93/1.03  --dbg_dump_prop_clauses_file            -
% 2.93/1.03  --dbg_out_stat                          false
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  ------ Proving...
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  % SZS status Theorem for theBenchmark.p
% 2.93/1.03  
% 2.93/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.93/1.03  
% 2.93/1.03  fof(f15,conjecture,(
% 2.93/1.03    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f16,negated_conjecture,(
% 2.93/1.03    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.93/1.03    inference(negated_conjecture,[],[f15])).
% 2.93/1.03  
% 2.93/1.03  fof(f36,plain,(
% 2.93/1.03    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 2.93/1.03    inference(ennf_transformation,[],[f16])).
% 2.93/1.03  
% 2.93/1.03  fof(f37,plain,(
% 2.93/1.03    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 2.93/1.03    inference(flattening,[],[f36])).
% 2.93/1.03  
% 2.93/1.03  fof(f45,plain,(
% 2.93/1.03    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k7_partfun1(X0,X4,k1_funct_1(X3,sK6)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK6) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK6,X1))) )),
% 2.93/1.03    introduced(choice_axiom,[])).
% 2.93/1.03  
% 2.93/1.03  fof(f44,plain,(
% 2.93/1.03    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k7_partfun1(X0,sK5,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK5),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK5)) & m1_subset_1(X5,X1)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK5))) )),
% 2.93/1.03    introduced(choice_axiom,[])).
% 2.93/1.03  
% 2.93/1.03  fof(f43,plain,(
% 2.93/1.03    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(sK4,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK4,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK4),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 2.93/1.03    introduced(choice_axiom,[])).
% 2.93/1.03  
% 2.93/1.03  fof(f42,plain,(
% 2.93/1.03    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(sK1,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))),
% 2.93/1.03    introduced(choice_axiom,[])).
% 2.93/1.03  
% 2.93/1.03  fof(f46,plain,(
% 2.93/1.03    (((k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) & m1_subset_1(sK6,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 2.93/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f37,f45,f44,f43,f42])).
% 2.93/1.03  
% 2.93/1.03  fof(f73,plain,(
% 2.93/1.03    m1_subset_1(sK6,sK2)),
% 2.93/1.03    inference(cnf_transformation,[],[f46])).
% 2.93/1.03  
% 2.93/1.03  fof(f3,axiom,(
% 2.93/1.03    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f20,plain,(
% 2.93/1.03    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.93/1.03    inference(ennf_transformation,[],[f3])).
% 2.93/1.03  
% 2.93/1.03  fof(f21,plain,(
% 2.93/1.03    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.93/1.03    inference(flattening,[],[f20])).
% 2.93/1.03  
% 2.93/1.03  fof(f49,plain,(
% 2.93/1.03    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.93/1.03    inference(cnf_transformation,[],[f21])).
% 2.93/1.03  
% 2.93/1.03  fof(f75,plain,(
% 2.93/1.03    k1_xboole_0 != sK2),
% 2.93/1.03    inference(cnf_transformation,[],[f46])).
% 2.93/1.03  
% 2.93/1.03  fof(f10,axiom,(
% 2.93/1.03    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f17,plain,(
% 2.93/1.03    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.93/1.03    inference(pure_predicate_removal,[],[f10])).
% 2.93/1.03  
% 2.93/1.03  fof(f27,plain,(
% 2.93/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.93/1.03    inference(ennf_transformation,[],[f17])).
% 2.93/1.03  
% 2.93/1.03  fof(f39,plain,(
% 2.93/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.93/1.03    introduced(choice_axiom,[])).
% 2.93/1.03  
% 2.93/1.03  fof(f40,plain,(
% 2.93/1.03    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 2.93/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f39])).
% 2.93/1.03  
% 2.93/1.03  fof(f57,plain,(
% 2.93/1.03    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.93/1.03    inference(cnf_transformation,[],[f40])).
% 2.93/1.03  
% 2.93/1.03  fof(f2,axiom,(
% 2.93/1.03    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f19,plain,(
% 2.93/1.03    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 2.93/1.03    inference(ennf_transformation,[],[f2])).
% 2.93/1.03  
% 2.93/1.03  fof(f48,plain,(
% 2.93/1.03    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 2.93/1.03    inference(cnf_transformation,[],[f19])).
% 2.93/1.03  
% 2.93/1.03  fof(f72,plain,(
% 2.93/1.03    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.93/1.03    inference(cnf_transformation,[],[f46])).
% 2.93/1.03  
% 2.93/1.03  fof(f7,axiom,(
% 2.93/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f18,plain,(
% 2.93/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.93/1.03    inference(pure_predicate_removal,[],[f7])).
% 2.93/1.03  
% 2.93/1.03  fof(f24,plain,(
% 2.93/1.03    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.03    inference(ennf_transformation,[],[f18])).
% 2.93/1.03  
% 2.93/1.03  fof(f54,plain,(
% 2.93/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/1.03    inference(cnf_transformation,[],[f24])).
% 2.93/1.03  
% 2.93/1.03  fof(f70,plain,(
% 2.93/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.93/1.03    inference(cnf_transformation,[],[f46])).
% 2.93/1.03  
% 2.93/1.03  fof(f9,axiom,(
% 2.93/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f26,plain,(
% 2.93/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.03    inference(ennf_transformation,[],[f9])).
% 2.93/1.03  
% 2.93/1.03  fof(f56,plain,(
% 2.93/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/1.03    inference(cnf_transformation,[],[f26])).
% 2.93/1.03  
% 2.93/1.03  fof(f74,plain,(
% 2.93/1.03    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))),
% 2.93/1.03    inference(cnf_transformation,[],[f46])).
% 2.93/1.03  
% 2.93/1.03  fof(f8,axiom,(
% 2.93/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f25,plain,(
% 2.93/1.03    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.03    inference(ennf_transformation,[],[f8])).
% 2.93/1.03  
% 2.93/1.03  fof(f55,plain,(
% 2.93/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/1.03    inference(cnf_transformation,[],[f25])).
% 2.93/1.03  
% 2.93/1.03  fof(f5,axiom,(
% 2.93/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f23,plain,(
% 2.93/1.03    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.93/1.03    inference(ennf_transformation,[],[f5])).
% 2.93/1.03  
% 2.93/1.03  fof(f38,plain,(
% 2.93/1.03    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.93/1.03    inference(nnf_transformation,[],[f23])).
% 2.93/1.03  
% 2.93/1.03  fof(f52,plain,(
% 2.93/1.03    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.93/1.03    inference(cnf_transformation,[],[f38])).
% 2.93/1.03  
% 2.93/1.03  fof(f4,axiom,(
% 2.93/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f22,plain,(
% 2.93/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.93/1.03    inference(ennf_transformation,[],[f4])).
% 2.93/1.03  
% 2.93/1.03  fof(f50,plain,(
% 2.93/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.93/1.03    inference(cnf_transformation,[],[f22])).
% 2.93/1.03  
% 2.93/1.03  fof(f6,axiom,(
% 2.93/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f53,plain,(
% 2.93/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.93/1.03    inference(cnf_transformation,[],[f6])).
% 2.93/1.03  
% 2.93/1.03  fof(f14,axiom,(
% 2.93/1.03    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => r2_hidden(k1_funct_1(X2,X1),X0)))),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f34,plain,(
% 2.93/1.03    ! [X0,X1,X2] : ((r2_hidden(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 2.93/1.03    inference(ennf_transformation,[],[f14])).
% 2.93/1.03  
% 2.93/1.03  fof(f35,plain,(
% 2.93/1.03    ! [X0,X1,X2] : (r2_hidden(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 2.93/1.03    inference(flattening,[],[f34])).
% 2.93/1.03  
% 2.93/1.03  fof(f66,plain,(
% 2.93/1.03    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 2.93/1.03    inference(cnf_transformation,[],[f35])).
% 2.93/1.03  
% 2.93/1.03  fof(f12,axiom,(
% 2.93/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f30,plain,(
% 2.93/1.03    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.93/1.03    inference(ennf_transformation,[],[f12])).
% 2.93/1.03  
% 2.93/1.03  fof(f31,plain,(
% 2.93/1.03    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.93/1.03    inference(flattening,[],[f30])).
% 2.93/1.03  
% 2.93/1.03  fof(f64,plain,(
% 2.93/1.03    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.93/1.03    inference(cnf_transformation,[],[f31])).
% 2.93/1.03  
% 2.93/1.03  fof(f11,axiom,(
% 2.93/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f28,plain,(
% 2.93/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.03    inference(ennf_transformation,[],[f11])).
% 2.93/1.03  
% 2.93/1.03  fof(f29,plain,(
% 2.93/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.03    inference(flattening,[],[f28])).
% 2.93/1.03  
% 2.93/1.03  fof(f41,plain,(
% 2.93/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.03    inference(nnf_transformation,[],[f29])).
% 2.93/1.03  
% 2.93/1.03  fof(f58,plain,(
% 2.93/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/1.03    inference(cnf_transformation,[],[f41])).
% 2.93/1.03  
% 2.93/1.03  fof(f69,plain,(
% 2.93/1.03    v1_funct_2(sK4,sK2,sK3)),
% 2.93/1.03    inference(cnf_transformation,[],[f46])).
% 2.93/1.03  
% 2.93/1.03  fof(f1,axiom,(
% 2.93/1.03    v1_xboole_0(k1_xboole_0)),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f47,plain,(
% 2.93/1.03    v1_xboole_0(k1_xboole_0)),
% 2.93/1.03    inference(cnf_transformation,[],[f1])).
% 2.93/1.03  
% 2.93/1.03  fof(f67,plain,(
% 2.93/1.03    ~v1_xboole_0(sK3)),
% 2.93/1.03    inference(cnf_transformation,[],[f46])).
% 2.93/1.03  
% 2.93/1.03  fof(f68,plain,(
% 2.93/1.03    v1_funct_1(sK4)),
% 2.93/1.03    inference(cnf_transformation,[],[f46])).
% 2.93/1.03  
% 2.93/1.03  fof(f71,plain,(
% 2.93/1.03    v1_funct_1(sK5)),
% 2.93/1.03    inference(cnf_transformation,[],[f46])).
% 2.93/1.03  
% 2.93/1.03  fof(f13,axiom,(
% 2.93/1.03    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f32,plain,(
% 2.93/1.03    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.93/1.03    inference(ennf_transformation,[],[f13])).
% 2.93/1.03  
% 2.93/1.03  fof(f33,plain,(
% 2.93/1.03    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.93/1.03    inference(flattening,[],[f32])).
% 2.93/1.03  
% 2.93/1.03  fof(f65,plain,(
% 2.93/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 2.93/1.03    inference(cnf_transformation,[],[f33])).
% 2.93/1.03  
% 2.93/1.03  fof(f76,plain,(
% 2.93/1.03    k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6)),
% 2.93/1.03    inference(cnf_transformation,[],[f46])).
% 2.93/1.03  
% 2.93/1.03  cnf(c_23,negated_conjecture,
% 2.93/1.03      ( m1_subset_1(sK6,sK2) ),
% 2.93/1.03      inference(cnf_transformation,[],[f73]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2054,plain,
% 2.93/1.03      ( m1_subset_1(sK6,sK2) = iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2,plain,
% 2.93/1.03      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.93/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2066,plain,
% 2.93/1.03      ( m1_subset_1(X0,X1) != iProver_top
% 2.93/1.03      | r2_hidden(X0,X1) = iProver_top
% 2.93/1.03      | v1_xboole_0(X1) = iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2882,plain,
% 2.93/1.03      ( r2_hidden(sK6,sK2) = iProver_top
% 2.93/1.03      | v1_xboole_0(sK2) = iProver_top ),
% 2.93/1.03      inference(superposition,[status(thm)],[c_2054,c_2066]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_21,negated_conjecture,
% 2.93/1.03      ( k1_xboole_0 != sK2 ),
% 2.93/1.03      inference(cnf_transformation,[],[f75]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_10,plain,
% 2.93/1.03      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.93/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2263,plain,
% 2.93/1.03      ( r2_hidden(sK0(sK2),sK2) | k1_xboole_0 = sK2 ),
% 2.93/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2264,plain,
% 2.93/1.03      ( k1_xboole_0 = sK2 | r2_hidden(sK0(sK2),sK2) = iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_2263]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_1,plain,
% 2.93/1.03      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.93/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2379,plain,
% 2.93/1.03      ( ~ r2_hidden(sK0(sK2),sK2) | ~ v1_xboole_0(sK2) ),
% 2.93/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2380,plain,
% 2.93/1.03      ( r2_hidden(sK0(sK2),sK2) != iProver_top
% 2.93/1.03      | v1_xboole_0(sK2) != iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_2379]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_3588,plain,
% 2.93/1.03      ( r2_hidden(sK6,sK2) = iProver_top ),
% 2.93/1.03      inference(global_propositional_subsumption,
% 2.93/1.03                [status(thm)],
% 2.93/1.03                [c_2882,c_21,c_2264,c_2380]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_24,negated_conjecture,
% 2.93/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 2.93/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2053,plain,
% 2.93/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_7,plain,
% 2.93/1.03      ( v5_relat_1(X0,X1)
% 2.93/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.93/1.03      inference(cnf_transformation,[],[f54]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2061,plain,
% 2.93/1.03      ( v5_relat_1(X0,X1) = iProver_top
% 2.93/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2780,plain,
% 2.93/1.03      ( v5_relat_1(sK5,sK1) = iProver_top ),
% 2.93/1.03      inference(superposition,[status(thm)],[c_2053,c_2061]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_26,negated_conjecture,
% 2.93/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.93/1.03      inference(cnf_transformation,[],[f70]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2051,plain,
% 2.93/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_9,plain,
% 2.93/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.93/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2059,plain,
% 2.93/1.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.93/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2792,plain,
% 2.93/1.03      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 2.93/1.03      inference(superposition,[status(thm)],[c_2051,c_2059]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_22,negated_conjecture,
% 2.93/1.03      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
% 2.93/1.03      inference(cnf_transformation,[],[f74]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2055,plain,
% 2.93/1.03      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_3015,plain,
% 2.93/1.03      ( r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
% 2.93/1.03      inference(demodulation,[status(thm)],[c_2792,c_2055]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_8,plain,
% 2.93/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.93/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2060,plain,
% 2.93/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.93/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2872,plain,
% 2.93/1.03      ( k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5) ),
% 2.93/1.03      inference(superposition,[status(thm)],[c_2053,c_2060]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_3157,plain,
% 2.93/1.03      ( r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) = iProver_top ),
% 2.93/1.03      inference(light_normalisation,[status(thm)],[c_3015,c_2872]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_4,plain,
% 2.93/1.03      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.93/1.03      | v5_relat_1(X0,X1)
% 2.93/1.03      | ~ v1_relat_1(X0) ),
% 2.93/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2064,plain,
% 2.93/1.03      ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.93/1.03      | v5_relat_1(X0,X1) = iProver_top
% 2.93/1.03      | v1_relat_1(X0) != iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_3345,plain,
% 2.93/1.03      ( v5_relat_1(sK4,k1_relat_1(sK5)) = iProver_top
% 2.93/1.03      | v1_relat_1(sK4) != iProver_top ),
% 2.93/1.03      inference(superposition,[status(thm)],[c_3157,c_2064]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_33,plain,
% 2.93/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_3,plain,
% 2.93/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.93/1.03      | ~ v1_relat_1(X1)
% 2.93/1.03      | v1_relat_1(X0) ),
% 2.93/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2266,plain,
% 2.93/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/1.03      | v1_relat_1(X0)
% 2.93/1.03      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.93/1.03      inference(instantiation,[status(thm)],[c_3]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2411,plain,
% 2.93/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.93/1.03      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
% 2.93/1.03      | v1_relat_1(sK4) ),
% 2.93/1.03      inference(instantiation,[status(thm)],[c_2266]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2412,plain,
% 2.93/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.93/1.03      | v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 2.93/1.03      | v1_relat_1(sK4) = iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_2411]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_6,plain,
% 2.93/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.93/1.03      inference(cnf_transformation,[],[f53]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2432,plain,
% 2.93/1.03      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.93/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2433,plain,
% 2.93/1.03      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_2432]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_3913,plain,
% 2.93/1.03      ( v5_relat_1(sK4,k1_relat_1(sK5)) = iProver_top ),
% 2.93/1.03      inference(global_propositional_subsumption,
% 2.93/1.03                [status(thm)],
% 2.93/1.03                [c_3345,c_33,c_2412,c_2433]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_19,plain,
% 2.93/1.03      ( ~ v5_relat_1(X0,X1)
% 2.93/1.03      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.93/1.03      | r2_hidden(k1_funct_1(X0,X2),X1)
% 2.93/1.03      | ~ v1_funct_1(X0)
% 2.93/1.03      | ~ v1_relat_1(X0) ),
% 2.93/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2056,plain,
% 2.93/1.03      ( v5_relat_1(X0,X1) != iProver_top
% 2.93/1.03      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 2.93/1.03      | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
% 2.93/1.03      | v1_funct_1(X0) != iProver_top
% 2.93/1.03      | v1_relat_1(X0) != iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_17,plain,
% 2.93/1.03      ( ~ v5_relat_1(X0,X1)
% 2.93/1.03      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.93/1.03      | ~ v1_funct_1(X0)
% 2.93/1.03      | ~ v1_relat_1(X0)
% 2.93/1.03      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.93/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2057,plain,
% 2.93/1.03      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 2.93/1.03      | v5_relat_1(X1,X0) != iProver_top
% 2.93/1.03      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 2.93/1.03      | v1_funct_1(X1) != iProver_top
% 2.93/1.03      | v1_relat_1(X1) != iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_3449,plain,
% 2.93/1.03      ( k7_partfun1(X0,X1,k1_funct_1(X2,X3)) = k1_funct_1(X1,k1_funct_1(X2,X3))
% 2.93/1.03      | v5_relat_1(X1,X0) != iProver_top
% 2.93/1.03      | v5_relat_1(X2,k1_relat_1(X1)) != iProver_top
% 2.93/1.03      | r2_hidden(X3,k1_relat_1(X2)) != iProver_top
% 2.93/1.03      | v1_funct_1(X2) != iProver_top
% 2.93/1.03      | v1_funct_1(X1) != iProver_top
% 2.93/1.03      | v1_relat_1(X2) != iProver_top
% 2.93/1.03      | v1_relat_1(X1) != iProver_top ),
% 2.93/1.03      inference(superposition,[status(thm)],[c_2056,c_2057]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_5359,plain,
% 2.93/1.03      ( k7_partfun1(X0,sK5,k1_funct_1(sK4,X1)) = k1_funct_1(sK5,k1_funct_1(sK4,X1))
% 2.93/1.03      | v5_relat_1(sK5,X0) != iProver_top
% 2.93/1.03      | r2_hidden(X1,k1_relat_1(sK4)) != iProver_top
% 2.93/1.03      | v1_funct_1(sK4) != iProver_top
% 2.93/1.03      | v1_funct_1(sK5) != iProver_top
% 2.93/1.03      | v1_relat_1(sK4) != iProver_top
% 2.93/1.03      | v1_relat_1(sK5) != iProver_top ),
% 2.93/1.03      inference(superposition,[status(thm)],[c_3913,c_3449]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2873,plain,
% 2.93/1.03      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.93/1.03      inference(superposition,[status(thm)],[c_2051,c_2060]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_16,plain,
% 2.93/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.93/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/1.03      | k1_relset_1(X1,X2,X0) = X1
% 2.93/1.03      | k1_xboole_0 = X2 ),
% 2.93/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_27,negated_conjecture,
% 2.93/1.03      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.93/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_759,plain,
% 2.93/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/1.03      | k1_relset_1(X1,X2,X0) = X1
% 2.93/1.03      | sK3 != X2
% 2.93/1.03      | sK2 != X1
% 2.93/1.03      | sK4 != X0
% 2.93/1.03      | k1_xboole_0 = X2 ),
% 2.93/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_760,plain,
% 2.93/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.93/1.03      | k1_relset_1(sK2,sK3,sK4) = sK2
% 2.93/1.03      | k1_xboole_0 = sK3 ),
% 2.93/1.03      inference(unflattening,[status(thm)],[c_759]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_762,plain,
% 2.93/1.03      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 2.93/1.03      inference(global_propositional_subsumption,
% 2.93/1.03                [status(thm)],
% 2.93/1.03                [c_760,c_26]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_3083,plain,
% 2.93/1.03      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.93/1.03      inference(superposition,[status(thm)],[c_2873,c_762]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_0,plain,
% 2.93/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 2.93/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_29,negated_conjecture,
% 2.93/1.03      ( ~ v1_xboole_0(sK3) ),
% 2.93/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_333,plain,
% 2.93/1.03      ( sK3 != k1_xboole_0 ),
% 2.93/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_29]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_3160,plain,
% 2.93/1.03      ( k1_relat_1(sK4) = sK2 ),
% 2.93/1.03      inference(global_propositional_subsumption,
% 2.93/1.03                [status(thm)],
% 2.93/1.03                [c_3083,c_333]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_5384,plain,
% 2.93/1.03      ( k7_partfun1(X0,sK5,k1_funct_1(sK4,X1)) = k1_funct_1(sK5,k1_funct_1(sK4,X1))
% 2.93/1.03      | v5_relat_1(sK5,X0) != iProver_top
% 2.93/1.03      | r2_hidden(X1,sK2) != iProver_top
% 2.93/1.03      | v1_funct_1(sK4) != iProver_top
% 2.93/1.03      | v1_funct_1(sK5) != iProver_top
% 2.93/1.03      | v1_relat_1(sK4) != iProver_top
% 2.93/1.03      | v1_relat_1(sK5) != iProver_top ),
% 2.93/1.03      inference(light_normalisation,[status(thm)],[c_5359,c_3160]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_28,negated_conjecture,
% 2.93/1.03      ( v1_funct_1(sK4) ),
% 2.93/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_31,plain,
% 2.93/1.03      ( v1_funct_1(sK4) = iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_25,negated_conjecture,
% 2.93/1.03      ( v1_funct_1(sK5) ),
% 2.93/1.03      inference(cnf_transformation,[],[f71]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_34,plain,
% 2.93/1.03      ( v1_funct_1(sK5) = iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_35,plain,
% 2.93/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2408,plain,
% 2.93/1.03      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 2.93/1.03      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
% 2.93/1.03      | v1_relat_1(sK5) ),
% 2.93/1.03      inference(instantiation,[status(thm)],[c_2266]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2409,plain,
% 2.93/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 2.93/1.03      | v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
% 2.93/1.03      | v1_relat_1(sK5) = iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_2408]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2429,plain,
% 2.93/1.03      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) ),
% 2.93/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2430,plain,
% 2.93/1.03      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_2429]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_6395,plain,
% 2.93/1.03      ( k7_partfun1(X0,sK5,k1_funct_1(sK4,X1)) = k1_funct_1(sK5,k1_funct_1(sK4,X1))
% 2.93/1.03      | v5_relat_1(sK5,X0) != iProver_top
% 2.93/1.03      | r2_hidden(X1,sK2) != iProver_top ),
% 2.93/1.03      inference(global_propositional_subsumption,
% 2.93/1.03                [status(thm)],
% 2.93/1.03                [c_5384,c_31,c_33,c_34,c_35,c_2409,c_2412,c_2430,c_2433]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_6404,plain,
% 2.93/1.03      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,X0)) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
% 2.93/1.03      | r2_hidden(X0,sK2) != iProver_top ),
% 2.93/1.03      inference(superposition,[status(thm)],[c_2780,c_6395]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_6413,plain,
% 2.93/1.03      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
% 2.93/1.03      inference(superposition,[status(thm)],[c_3588,c_6404]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_18,plain,
% 2.93/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.93/1.03      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 2.93/1.03      | ~ m1_subset_1(X5,X1)
% 2.93/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.93/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/1.03      | ~ v1_funct_1(X4)
% 2.93/1.03      | ~ v1_funct_1(X0)
% 2.93/1.03      | v1_xboole_0(X2)
% 2.93/1.03      | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k1_funct_1(X4,k1_funct_1(X0,X5))
% 2.93/1.03      | k1_xboole_0 = X1 ),
% 2.93/1.03      inference(cnf_transformation,[],[f65]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_732,plain,
% 2.93/1.03      ( ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,X4))
% 2.93/1.03      | ~ m1_subset_1(X5,X0)
% 2.93/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.93/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.93/1.03      | ~ v1_funct_1(X2)
% 2.93/1.03      | ~ v1_funct_1(X4)
% 2.93/1.03      | v1_xboole_0(X1)
% 2.93/1.03      | k1_funct_1(k8_funct_2(X0,X1,X3,X2,X4),X5) = k1_funct_1(X4,k1_funct_1(X2,X5))
% 2.93/1.03      | sK3 != X1
% 2.93/1.03      | sK2 != X0
% 2.93/1.03      | sK4 != X2
% 2.93/1.03      | k1_xboole_0 = X0 ),
% 2.93/1.03      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_733,plain,
% 2.93/1.03      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1))
% 2.93/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
% 2.93/1.03      | ~ m1_subset_1(X2,sK2)
% 2.93/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.93/1.03      | ~ v1_funct_1(X1)
% 2.93/1.03      | ~ v1_funct_1(sK4)
% 2.93/1.03      | v1_xboole_0(sK3)
% 2.93/1.03      | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))
% 2.93/1.03      | k1_xboole_0 = sK2 ),
% 2.93/1.03      inference(unflattening,[status(thm)],[c_732]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_737,plain,
% 2.93/1.03      ( k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))
% 2.93/1.03      | ~ v1_funct_1(X1)
% 2.93/1.03      | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1))
% 2.93/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
% 2.93/1.03      | ~ m1_subset_1(X2,sK2) ),
% 2.93/1.03      inference(global_propositional_subsumption,
% 2.93/1.03                [status(thm)],
% 2.93/1.03                [c_733,c_29,c_28,c_26,c_21]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_738,plain,
% 2.93/1.03      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1))
% 2.93/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
% 2.93/1.03      | ~ m1_subset_1(X2,sK2)
% 2.93/1.03      | ~ v1_funct_1(X1)
% 2.93/1.03      | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2)) ),
% 2.93/1.03      inference(renaming,[status(thm)],[c_737]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2046,plain,
% 2.93/1.03      ( k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))
% 2.93/1.03      | r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
% 2.93/1.03      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
% 2.93/1.03      | m1_subset_1(X2,sK2) != iProver_top
% 2.93/1.03      | v1_funct_1(X1) != iProver_top ),
% 2.93/1.03      inference(predicate_to_equality,[status(thm)],[c_738]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2574,plain,
% 2.93/1.03      ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
% 2.93/1.03      | m1_subset_1(X0,sK2) != iProver_top
% 2.93/1.03      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 2.93/1.03      | v1_funct_1(sK5) != iProver_top ),
% 2.93/1.03      inference(superposition,[status(thm)],[c_2055,c_2046]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2636,plain,
% 2.93/1.03      ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
% 2.93/1.03      | m1_subset_1(X0,sK2) != iProver_top ),
% 2.93/1.03      inference(global_propositional_subsumption,
% 2.93/1.03                [status(thm)],
% 2.93/1.03                [c_2574,c_34,c_35]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2644,plain,
% 2.93/1.03      ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
% 2.93/1.03      inference(superposition,[status(thm)],[c_2054,c_2636]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_20,negated_conjecture,
% 2.93/1.03      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
% 2.93/1.03      inference(cnf_transformation,[],[f76]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2646,plain,
% 2.93/1.03      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
% 2.93/1.03      inference(demodulation,[status(thm)],[c_2644,c_20]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(contradiction,plain,
% 2.93/1.03      ( $false ),
% 2.93/1.03      inference(minisat,[status(thm)],[c_6413,c_2646]) ).
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.93/1.03  
% 2.93/1.03  ------                               Statistics
% 2.93/1.03  
% 2.93/1.03  ------ General
% 2.93/1.03  
% 2.93/1.03  abstr_ref_over_cycles:                  0
% 2.93/1.03  abstr_ref_under_cycles:                 0
% 2.93/1.03  gc_basic_clause_elim:                   0
% 2.93/1.03  forced_gc_time:                         0
% 2.93/1.03  parsing_time:                           0.016
% 2.93/1.03  unif_index_cands_time:                  0.
% 2.93/1.03  unif_index_add_time:                    0.
% 2.93/1.03  orderings_time:                         0.
% 2.93/1.03  out_proof_time:                         0.012
% 2.93/1.03  total_time:                             0.189
% 2.93/1.03  num_of_symbols:                         56
% 2.93/1.03  num_of_terms:                           5396
% 2.93/1.03  
% 2.93/1.03  ------ Preprocessing
% 2.93/1.03  
% 2.93/1.03  num_of_splits:                          0
% 2.93/1.03  num_of_split_atoms:                     0
% 2.93/1.03  num_of_reused_defs:                     0
% 2.93/1.03  num_eq_ax_congr_red:                    15
% 2.93/1.03  num_of_sem_filtered_clauses:            1
% 2.93/1.03  num_of_subtypes:                        0
% 2.93/1.03  monotx_restored_types:                  0
% 2.93/1.03  sat_num_of_epr_types:                   0
% 2.93/1.03  sat_num_of_non_cyclic_types:            0
% 2.93/1.03  sat_guarded_non_collapsed_types:        0
% 2.93/1.03  num_pure_diseq_elim:                    0
% 2.93/1.03  simp_replaced_by:                       0
% 2.93/1.03  res_preprocessed:                       142
% 2.93/1.03  prep_upred:                             0
% 2.93/1.03  prep_unflattend:                        54
% 2.93/1.03  smt_new_axioms:                         0
% 2.93/1.03  pred_elim_cands:                        7
% 2.93/1.03  pred_elim:                              1
% 2.93/1.03  pred_elim_cl:                           3
% 2.93/1.03  pred_elim_cycles:                       9
% 2.93/1.03  merged_defs:                            0
% 2.93/1.03  merged_defs_ncl:                        0
% 2.93/1.03  bin_hyper_res:                          0
% 2.93/1.03  prep_cycles:                            4
% 2.93/1.03  pred_elim_time:                         0.016
% 2.93/1.03  splitting_time:                         0.
% 2.93/1.03  sem_filter_time:                        0.
% 2.93/1.03  monotx_time:                            0.
% 2.93/1.03  subtype_inf_time:                       0.
% 2.93/1.03  
% 2.93/1.03  ------ Problem properties
% 2.93/1.03  
% 2.93/1.03  clauses:                                27
% 2.93/1.03  conjectures:                            9
% 2.93/1.03  epr:                                    9
% 2.93/1.03  horn:                                   23
% 2.93/1.03  ground:                                 13
% 2.93/1.03  unary:                                  12
% 2.93/1.03  binary:                                 6
% 2.93/1.03  lits:                                   65
% 2.93/1.03  lits_eq:                                16
% 2.93/1.03  fd_pure:                                0
% 2.93/1.03  fd_pseudo:                              0
% 2.93/1.03  fd_cond:                                2
% 2.93/1.03  fd_pseudo_cond:                         0
% 2.93/1.03  ac_symbols:                             0
% 2.93/1.03  
% 2.93/1.03  ------ Propositional Solver
% 2.93/1.03  
% 2.93/1.03  prop_solver_calls:                      29
% 2.93/1.03  prop_fast_solver_calls:                 1323
% 2.93/1.03  smt_solver_calls:                       0
% 2.93/1.03  smt_fast_solver_calls:                  0
% 2.93/1.03  prop_num_of_clauses:                    1842
% 2.93/1.03  prop_preprocess_simplified:             6291
% 2.93/1.03  prop_fo_subsumed:                       50
% 2.93/1.03  prop_solver_time:                       0.
% 2.93/1.03  smt_solver_time:                        0.
% 2.93/1.03  smt_fast_solver_time:                   0.
% 2.93/1.03  prop_fast_solver_time:                  0.
% 2.93/1.03  prop_unsat_core_time:                   0.
% 2.93/1.03  
% 2.93/1.03  ------ QBF
% 2.93/1.03  
% 2.93/1.03  qbf_q_res:                              0
% 2.93/1.03  qbf_num_tautologies:                    0
% 2.93/1.03  qbf_prep_cycles:                        0
% 2.93/1.03  
% 2.93/1.03  ------ BMC1
% 2.93/1.03  
% 2.93/1.03  bmc1_current_bound:                     -1
% 2.93/1.03  bmc1_last_solved_bound:                 -1
% 2.93/1.03  bmc1_unsat_core_size:                   -1
% 2.93/1.03  bmc1_unsat_core_parents_size:           -1
% 2.93/1.03  bmc1_merge_next_fun:                    0
% 2.93/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.93/1.03  
% 2.93/1.03  ------ Instantiation
% 2.93/1.03  
% 2.93/1.03  inst_num_of_clauses:                    776
% 2.93/1.03  inst_num_in_passive:                    411
% 2.93/1.03  inst_num_in_active:                     345
% 2.93/1.03  inst_num_in_unprocessed:                20
% 2.93/1.03  inst_num_of_loops:                      400
% 2.93/1.03  inst_num_of_learning_restarts:          0
% 2.93/1.03  inst_num_moves_active_passive:          52
% 2.93/1.03  inst_lit_activity:                      0
% 2.93/1.03  inst_lit_activity_moves:                0
% 2.93/1.03  inst_num_tautologies:                   0
% 2.93/1.03  inst_num_prop_implied:                  0
% 2.93/1.03  inst_num_existing_simplified:           0
% 2.93/1.03  inst_num_eq_res_simplified:             0
% 2.93/1.03  inst_num_child_elim:                    0
% 2.93/1.03  inst_num_of_dismatching_blockings:      83
% 2.93/1.03  inst_num_of_non_proper_insts:           445
% 2.93/1.03  inst_num_of_duplicates:                 0
% 2.93/1.03  inst_inst_num_from_inst_to_res:         0
% 2.93/1.03  inst_dismatching_checking_time:         0.
% 2.93/1.03  
% 2.93/1.03  ------ Resolution
% 2.93/1.03  
% 2.93/1.03  res_num_of_clauses:                     0
% 2.93/1.03  res_num_in_passive:                     0
% 2.93/1.03  res_num_in_active:                      0
% 2.93/1.03  res_num_of_loops:                       146
% 2.93/1.03  res_forward_subset_subsumed:            59
% 2.93/1.03  res_backward_subset_subsumed:           0
% 2.93/1.03  res_forward_subsumed:                   0
% 2.93/1.03  res_backward_subsumed:                  0
% 2.93/1.03  res_forward_subsumption_resolution:     0
% 2.93/1.03  res_backward_subsumption_resolution:    0
% 2.93/1.03  res_clause_to_clause_subsumption:       396
% 2.93/1.03  res_orphan_elimination:                 0
% 2.93/1.03  res_tautology_del:                      79
% 2.93/1.03  res_num_eq_res_simplified:              0
% 2.93/1.03  res_num_sel_changes:                    0
% 2.93/1.03  res_moves_from_active_to_pass:          0
% 2.93/1.03  
% 2.93/1.03  ------ Superposition
% 2.93/1.03  
% 2.93/1.03  sup_time_total:                         0.
% 2.93/1.03  sup_time_generating:                    0.
% 2.93/1.03  sup_time_sim_full:                      0.
% 2.93/1.03  sup_time_sim_immed:                     0.
% 2.93/1.03  
% 2.93/1.03  sup_num_of_clauses:                     91
% 2.93/1.03  sup_num_in_active:                      75
% 2.93/1.03  sup_num_in_passive:                     16
% 2.93/1.03  sup_num_of_loops:                       79
% 2.93/1.03  sup_fw_superposition:                   68
% 2.93/1.03  sup_bw_superposition:                   8
% 2.93/1.03  sup_immediate_simplified:               13
% 2.93/1.03  sup_given_eliminated:                   0
% 2.93/1.03  comparisons_done:                       0
% 2.93/1.03  comparisons_avoided:                    15
% 2.93/1.03  
% 2.93/1.03  ------ Simplifications
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  sim_fw_subset_subsumed:                 4
% 2.93/1.03  sim_bw_subset_subsumed:                 1
% 2.93/1.03  sim_fw_subsumed:                        2
% 2.93/1.03  sim_bw_subsumed:                        0
% 2.93/1.03  sim_fw_subsumption_res:                 2
% 2.93/1.03  sim_bw_subsumption_res:                 0
% 2.93/1.03  sim_tautology_del:                      3
% 2.93/1.03  sim_eq_tautology_del:                   2
% 2.93/1.03  sim_eq_res_simp:                        0
% 2.93/1.03  sim_fw_demodulated:                     2
% 2.93/1.03  sim_bw_demodulated:                     4
% 2.93/1.03  sim_light_normalised:                   6
% 2.93/1.03  sim_joinable_taut:                      0
% 2.93/1.03  sim_joinable_simp:                      0
% 2.93/1.03  sim_ac_normalised:                      0
% 2.93/1.03  sim_smt_subsumption:                    0
% 2.93/1.03  
%------------------------------------------------------------------------------

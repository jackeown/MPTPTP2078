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
% DateTime   : Thu Dec  3 12:03:56 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  280 (2210 expanded)
%              Number of clauses        :  209 ( 962 expanded)
%              Number of leaves         :   24 ( 452 expanded)
%              Depth                    :   25
%              Number of atoms          :  845 (10989 expanded)
%              Number of equality atoms :  482 (3816 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f37,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f37])).

fof(f42,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f42])).

fof(f70,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

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
    inference(nnf_transformation,[],[f32])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f71,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f72,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f76,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1124,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1111,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_433,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_434,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_436,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_26])).

cnf(c_1110,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1117,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1666,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1110,c_1117])).

cnf(c_1738,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_436,c_1666])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1120,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1839,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1738,c_1120])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1119,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1512,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1110,c_1119])).

cnf(c_1936,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1839,c_1512])).

cnf(c_1937,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1936])).

cnf(c_1945,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1111,c_1937])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1115,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2299,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1110,c_1115])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1116,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2500,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2299,c_1116])).

cnf(c_4593,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X2,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2500,c_1115])).

cnf(c_12726,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1945,c_4593])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_90,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_691,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1252,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_694,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1185,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_694])).

cnf(c_1244,plain,
    ( ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != sK0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1185])).

cnf(c_1361,plain,
    ( ~ r1_tarski(sK0,sK0)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != sK0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1244])).

cnf(c_1362,plain,
    ( sK0 != sK0
    | k1_xboole_0 != sK0
    | r1_tarski(sK0,sK0) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1361])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != X0
    | sK1 != k1_xboole_0
    | sK0 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_366,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_1107,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_80,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_85,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_692,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1322,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_1323,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1322])).

cnf(c_1472,plain,
    ( k1_xboole_0 = sK0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1107,c_24,c_80,c_85,c_1323])).

cnf(c_1473,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(renaming,[status(thm)],[c_1472])).

cnf(c_5844,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5845,plain,
    ( r1_tarski(sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5844])).

cnf(c_7,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4324,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_9000,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4324])).

cnf(c_9003,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9000])).

cnf(c_2347,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1110,c_1116])).

cnf(c_2650,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2347,c_1115])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1118,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5035,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2650,c_1118])).

cnf(c_9281,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1738,c_5035])).

cnf(c_1169,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_1201,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1169])).

cnf(c_2502,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2299,c_1118])).

cnf(c_693,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_6464,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_693])).

cnf(c_6465,plain,
    ( sK0 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6464])).

cnf(c_6467,plain,
    ( sK0 != k1_xboole_0
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6465])).

cnf(c_9285,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9281,c_90,c_1201,c_1252,c_1473,c_2502,c_6467])).

cnf(c_9289,plain,
    ( r1_tarski(sK0,X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1124,c_9285])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_79,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_81,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_87,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_23,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_444,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_1162,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1178,plain,
    ( sK2 != X0
    | sK2 = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_1179,plain,
    ( sK2 = sK0
    | sK2 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1178])).

cnf(c_1214,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_1245,plain,
    ( sK0 != sK0
    | k1_xboole_0 != X0
    | r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1244])).

cnf(c_1255,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_1180,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_694])).

cnf(c_1239,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1180])).

cnf(c_1290,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1239])).

cnf(c_1308,plain,
    ( ~ v1_xboole_0(sK0)
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1309,plain,
    ( k1_xboole_0 = sK0
    | v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1308])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1326,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1466,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1514,plain,
    ( v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1512])).

cnf(c_1671,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_1672,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1671])).

cnf(c_1673,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1675,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1673])).

cnf(c_1506,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_1721,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
    | k1_xboole_0 != k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_1894,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(sK0,X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1895,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1894])).

cnf(c_1897,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1895])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1122,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2297,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1122,c_1115])).

cnf(c_2301,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2297])).

cnf(c_2300,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2297])).

cnf(c_2302,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2300])).

cnf(c_2330,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2415,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_1654,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_2630,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1654])).

cnf(c_2631,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2630])).

cnf(c_2863,plain,
    ( ~ v1_xboole_0(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_xboole_0 = k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3682,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3683,plain,
    ( k1_xboole_0 = sK3
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3682])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4280,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_4285,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_4658,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4660,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v1_xboole_0(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4658])).

cnf(c_6459,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_6460,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6459])).

cnf(c_6462,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6460])).

cnf(c_3670,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X2)
    | X2 != X1
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_694])).

cnf(c_6954,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
    | ~ r1_tarski(k7_relat_1(sK3,sK2),X1)
    | X0 != X1
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_3670])).

cnf(c_8319,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
    | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | X0 != sK3
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_6954])).

cnf(c_8322,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
    | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_8319])).

cnf(c_2037,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_8904,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2037])).

cnf(c_8910,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8904])).

cnf(c_9339,plain,
    ( v1_xboole_0(X0) != iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9289,c_28,c_26,c_25,c_80,c_81,c_87,c_0,c_90,c_444,c_1162,c_1179,c_1201,c_1214,c_1245,c_1252,c_1255,c_1290,c_1309,c_1326,c_1466,c_1514,c_1672,c_1675,c_1721,c_1897,c_2301,c_2302,c_2330,c_2415,c_2631,c_2863,c_3683,c_4280,c_4285,c_4660,c_6462,c_8322,c_8910,c_9000])).

cnf(c_9340,plain,
    ( r1_tarski(sK0,X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9339])).

cnf(c_9342,plain,
    ( r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9340])).

cnf(c_14792,plain,
    ( r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12726,c_28,c_80,c_0,c_1179,c_1193,c_1201,c_1214,c_1252,c_1410,c_1473,c_1490,c_1512,c_1672,c_1712,c_1724,c_2120,c_2155,c_2302,c_2331,c_2415,c_2543,c_2631,c_2990,c_3682,c_5076,c_6312,c_6466,c_9003])).

cnf(c_14793,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_14792])).

cnf(c_1121,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4591,plain,
    ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
    | r1_tarski(X1,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2500,c_1117])).

cnf(c_7182,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1945,c_4591])).

cnf(c_1165,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_1193,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1165])).

cnf(c_521,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_444])).

cnf(c_1103,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_521])).

cnf(c_29,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_445,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_1327,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1326])).

cnf(c_1409,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != sK0
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1103,c_29,c_31,c_445,c_1255,c_1327])).

cnf(c_1410,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1409])).

cnf(c_14,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_339,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_340,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_354,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_340,c_6])).

cnf(c_1108,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_1285,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1490,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1108,c_25,c_1214,c_1285,c_1290,c_1466,c_1473])).

cnf(c_1711,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1110,c_1118])).

cnf(c_1712,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1711])).

cnf(c_1723,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(X0,X1,X2,X3)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
    | k1_xboole_0 != k2_partfun1(X0,X1,X2,X3) ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_1724,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
    | k1_xboole_0 != k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1723])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1114,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2112,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1114,c_1118])).

cnf(c_2118,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(k2_partfun1(X1,X2,X0,X3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2112])).

cnf(c_2120,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | v1_xboole_0(k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2118])).

cnf(c_696,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1683,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_696])).

cnf(c_2152,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_1683])).

cnf(c_2153,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2152])).

cnf(c_2155,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2153])).

cnf(c_2331,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2330])).

cnf(c_2543,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_2988,plain,
    ( ~ v1_xboole_0(k2_partfun1(X0,X1,X2,X3))
    | k1_xboole_0 = k2_partfun1(X0,X1,X2,X3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2990,plain,
    ( ~ v1_xboole_0(k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2988])).

cnf(c_700,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_partfun1(X0,X2,X4,X6) = k2_partfun1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_5075,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(X0,X1,X2,X3)
    | sK2 != X3
    | sK3 != X2
    | sK1 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_700])).

cnf(c_5076,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | sK1 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5075])).

cnf(c_701,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_6310,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_6312,plain,
    ( ~ v1_funct_1(sK3)
    | v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_6310])).

cnf(c_6466,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6464])).

cnf(c_7205,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7182,c_28,c_80,c_0,c_1179,c_1193,c_1201,c_1214,c_1252,c_1410,c_1473,c_1490,c_1672,c_1712,c_1724,c_2120,c_2155,c_2302,c_2331,c_2415,c_2543,c_2631,c_2990,c_3682,c_5076,c_6312,c_6466])).

cnf(c_7211,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1121,c_7205])).

cnf(c_9070,plain,
    ( r1_tarski(sK2,X0) != iProver_top
    | k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7211,c_1512,c_7205,c_9003])).

cnf(c_9071,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9070])).

cnf(c_9076,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_1124,c_9071])).

cnf(c_1112,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2286,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1110,c_1112])).

cnf(c_2480,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2286,c_29])).

cnf(c_17,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X1
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_418,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_1104,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_419,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_1335,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_xboole_0 = sK1
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1104,c_29,c_31,c_419,c_1327])).

cnf(c_1336,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1335])).

cnf(c_2485,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2480,c_1336])).

cnf(c_9530,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9076,c_2485])).

cnf(c_9650,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9530,c_28,c_80,c_0,c_1179,c_1193,c_1201,c_1214,c_1252,c_1410,c_1473,c_1490,c_1672,c_1712,c_1724,c_1945,c_2120,c_2155,c_2302,c_2331,c_2415,c_2543,c_2631,c_2990,c_3682,c_5076,c_6312,c_6466])).

cnf(c_14808,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14793,c_9650])).

cnf(c_1436,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1437,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1436])).

cnf(c_14833,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14808,c_1437])).

cnf(c_14837,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1124,c_14833])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.86/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.86/0.99  
% 3.86/0.99  ------  iProver source info
% 3.86/0.99  
% 3.86/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.86/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.86/0.99  git: non_committed_changes: false
% 3.86/0.99  git: last_make_outside_of_git: false
% 3.86/0.99  
% 3.86/0.99  ------ 
% 3.86/0.99  
% 3.86/0.99  ------ Input Options
% 3.86/0.99  
% 3.86/0.99  --out_options                           all
% 3.86/0.99  --tptp_safe_out                         true
% 3.86/0.99  --problem_path                          ""
% 3.86/0.99  --include_path                          ""
% 3.86/0.99  --clausifier                            res/vclausify_rel
% 3.86/0.99  --clausifier_options                    ""
% 3.86/0.99  --stdin                                 false
% 3.86/0.99  --stats_out                             all
% 3.86/0.99  
% 3.86/0.99  ------ General Options
% 3.86/0.99  
% 3.86/0.99  --fof                                   false
% 3.86/0.99  --time_out_real                         305.
% 3.86/0.99  --time_out_virtual                      -1.
% 3.86/0.99  --symbol_type_check                     false
% 3.86/0.99  --clausify_out                          false
% 3.86/0.99  --sig_cnt_out                           false
% 3.86/0.99  --trig_cnt_out                          false
% 3.86/0.99  --trig_cnt_out_tolerance                1.
% 3.86/0.99  --trig_cnt_out_sk_spl                   false
% 3.86/0.99  --abstr_cl_out                          false
% 3.86/0.99  
% 3.86/0.99  ------ Global Options
% 3.86/0.99  
% 3.86/0.99  --schedule                              default
% 3.86/0.99  --add_important_lit                     false
% 3.86/0.99  --prop_solver_per_cl                    1000
% 3.86/0.99  --min_unsat_core                        false
% 3.86/0.99  --soft_assumptions                      false
% 3.86/0.99  --soft_lemma_size                       3
% 3.86/0.99  --prop_impl_unit_size                   0
% 3.86/0.99  --prop_impl_unit                        []
% 3.86/0.99  --share_sel_clauses                     true
% 3.86/0.99  --reset_solvers                         false
% 3.86/0.99  --bc_imp_inh                            [conj_cone]
% 3.86/0.99  --conj_cone_tolerance                   3.
% 3.86/0.99  --extra_neg_conj                        none
% 3.86/0.99  --large_theory_mode                     true
% 3.86/0.99  --prolific_symb_bound                   200
% 3.86/0.99  --lt_threshold                          2000
% 3.86/0.99  --clause_weak_htbl                      true
% 3.86/0.99  --gc_record_bc_elim                     false
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing Options
% 3.86/0.99  
% 3.86/0.99  --preprocessing_flag                    true
% 3.86/0.99  --time_out_prep_mult                    0.1
% 3.86/0.99  --splitting_mode                        input
% 3.86/0.99  --splitting_grd                         true
% 3.86/0.99  --splitting_cvd                         false
% 3.86/0.99  --splitting_cvd_svl                     false
% 3.86/0.99  --splitting_nvd                         32
% 3.86/0.99  --sub_typing                            true
% 3.86/0.99  --prep_gs_sim                           true
% 3.86/0.99  --prep_unflatten                        true
% 3.86/0.99  --prep_res_sim                          true
% 3.86/0.99  --prep_upred                            true
% 3.86/0.99  --prep_sem_filter                       exhaustive
% 3.86/0.99  --prep_sem_filter_out                   false
% 3.86/0.99  --pred_elim                             true
% 3.86/0.99  --res_sim_input                         true
% 3.86/0.99  --eq_ax_congr_red                       true
% 3.86/0.99  --pure_diseq_elim                       true
% 3.86/0.99  --brand_transform                       false
% 3.86/0.99  --non_eq_to_eq                          false
% 3.86/0.99  --prep_def_merge                        true
% 3.86/0.99  --prep_def_merge_prop_impl              false
% 3.86/0.99  --prep_def_merge_mbd                    true
% 3.86/0.99  --prep_def_merge_tr_red                 false
% 3.86/0.99  --prep_def_merge_tr_cl                  false
% 3.86/0.99  --smt_preprocessing                     true
% 3.86/0.99  --smt_ac_axioms                         fast
% 3.86/0.99  --preprocessed_out                      false
% 3.86/0.99  --preprocessed_stats                    false
% 3.86/0.99  
% 3.86/0.99  ------ Abstraction refinement Options
% 3.86/0.99  
% 3.86/0.99  --abstr_ref                             []
% 3.86/0.99  --abstr_ref_prep                        false
% 3.86/0.99  --abstr_ref_until_sat                   false
% 3.86/0.99  --abstr_ref_sig_restrict                funpre
% 3.86/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.86/0.99  --abstr_ref_under                       []
% 3.86/0.99  
% 3.86/0.99  ------ SAT Options
% 3.86/0.99  
% 3.86/0.99  --sat_mode                              false
% 3.86/0.99  --sat_fm_restart_options                ""
% 3.86/0.99  --sat_gr_def                            false
% 3.86/0.99  --sat_epr_types                         true
% 3.86/0.99  --sat_non_cyclic_types                  false
% 3.86/0.99  --sat_finite_models                     false
% 3.86/0.99  --sat_fm_lemmas                         false
% 3.86/0.99  --sat_fm_prep                           false
% 3.86/0.99  --sat_fm_uc_incr                        true
% 3.86/0.99  --sat_out_model                         small
% 3.86/0.99  --sat_out_clauses                       false
% 3.86/0.99  
% 3.86/0.99  ------ QBF Options
% 3.86/0.99  
% 3.86/0.99  --qbf_mode                              false
% 3.86/0.99  --qbf_elim_univ                         false
% 3.86/0.99  --qbf_dom_inst                          none
% 3.86/0.99  --qbf_dom_pre_inst                      false
% 3.86/0.99  --qbf_sk_in                             false
% 3.86/0.99  --qbf_pred_elim                         true
% 3.86/0.99  --qbf_split                             512
% 3.86/0.99  
% 3.86/0.99  ------ BMC1 Options
% 3.86/0.99  
% 3.86/0.99  --bmc1_incremental                      false
% 3.86/0.99  --bmc1_axioms                           reachable_all
% 3.86/0.99  --bmc1_min_bound                        0
% 3.86/0.99  --bmc1_max_bound                        -1
% 3.86/0.99  --bmc1_max_bound_default                -1
% 3.86/0.99  --bmc1_symbol_reachability              true
% 3.86/0.99  --bmc1_property_lemmas                  false
% 3.86/0.99  --bmc1_k_induction                      false
% 3.86/0.99  --bmc1_non_equiv_states                 false
% 3.86/0.99  --bmc1_deadlock                         false
% 3.86/0.99  --bmc1_ucm                              false
% 3.86/0.99  --bmc1_add_unsat_core                   none
% 3.86/0.99  --bmc1_unsat_core_children              false
% 3.86/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.86/0.99  --bmc1_out_stat                         full
% 3.86/0.99  --bmc1_ground_init                      false
% 3.86/0.99  --bmc1_pre_inst_next_state              false
% 3.86/0.99  --bmc1_pre_inst_state                   false
% 3.86/0.99  --bmc1_pre_inst_reach_state             false
% 3.86/0.99  --bmc1_out_unsat_core                   false
% 3.86/0.99  --bmc1_aig_witness_out                  false
% 3.86/0.99  --bmc1_verbose                          false
% 3.86/0.99  --bmc1_dump_clauses_tptp                false
% 3.86/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.86/0.99  --bmc1_dump_file                        -
% 3.86/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.86/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.86/0.99  --bmc1_ucm_extend_mode                  1
% 3.86/0.99  --bmc1_ucm_init_mode                    2
% 3.86/0.99  --bmc1_ucm_cone_mode                    none
% 3.86/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.86/0.99  --bmc1_ucm_relax_model                  4
% 3.86/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.86/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.86/0.99  --bmc1_ucm_layered_model                none
% 3.86/0.99  --bmc1_ucm_max_lemma_size               10
% 3.86/0.99  
% 3.86/0.99  ------ AIG Options
% 3.86/0.99  
% 3.86/0.99  --aig_mode                              false
% 3.86/0.99  
% 3.86/0.99  ------ Instantiation Options
% 3.86/0.99  
% 3.86/0.99  --instantiation_flag                    true
% 3.86/0.99  --inst_sos_flag                         true
% 3.86/0.99  --inst_sos_phase                        true
% 3.86/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.86/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.86/0.99  --inst_lit_sel_side                     num_symb
% 3.86/0.99  --inst_solver_per_active                1400
% 3.86/0.99  --inst_solver_calls_frac                1.
% 3.86/0.99  --inst_passive_queue_type               priority_queues
% 3.86/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.86/0.99  --inst_passive_queues_freq              [25;2]
% 3.86/0.99  --inst_dismatching                      true
% 3.86/0.99  --inst_eager_unprocessed_to_passive     true
% 3.86/0.99  --inst_prop_sim_given                   true
% 3.86/0.99  --inst_prop_sim_new                     false
% 3.86/0.99  --inst_subs_new                         false
% 3.86/0.99  --inst_eq_res_simp                      false
% 3.86/0.99  --inst_subs_given                       false
% 3.86/0.99  --inst_orphan_elimination               true
% 3.86/0.99  --inst_learning_loop_flag               true
% 3.86/0.99  --inst_learning_start                   3000
% 3.86/0.99  --inst_learning_factor                  2
% 3.86/0.99  --inst_start_prop_sim_after_learn       3
% 3.86/0.99  --inst_sel_renew                        solver
% 3.86/0.99  --inst_lit_activity_flag                true
% 3.86/0.99  --inst_restr_to_given                   false
% 3.86/0.99  --inst_activity_threshold               500
% 3.86/0.99  --inst_out_proof                        true
% 3.86/0.99  
% 3.86/0.99  ------ Resolution Options
% 3.86/0.99  
% 3.86/0.99  --resolution_flag                       true
% 3.86/0.99  --res_lit_sel                           adaptive
% 3.86/0.99  --res_lit_sel_side                      none
% 3.86/0.99  --res_ordering                          kbo
% 3.86/0.99  --res_to_prop_solver                    active
% 3.86/0.99  --res_prop_simpl_new                    false
% 3.86/0.99  --res_prop_simpl_given                  true
% 3.86/0.99  --res_passive_queue_type                priority_queues
% 3.86/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.86/0.99  --res_passive_queues_freq               [15;5]
% 3.86/0.99  --res_forward_subs                      full
% 3.86/0.99  --res_backward_subs                     full
% 3.86/0.99  --res_forward_subs_resolution           true
% 3.86/0.99  --res_backward_subs_resolution          true
% 3.86/0.99  --res_orphan_elimination                true
% 3.86/0.99  --res_time_limit                        2.
% 3.86/0.99  --res_out_proof                         true
% 3.86/0.99  
% 3.86/0.99  ------ Superposition Options
% 3.86/0.99  
% 3.86/0.99  --superposition_flag                    true
% 3.86/0.99  --sup_passive_queue_type                priority_queues
% 3.86/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.86/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.86/0.99  --demod_completeness_check              fast
% 3.86/0.99  --demod_use_ground                      true
% 3.86/0.99  --sup_to_prop_solver                    passive
% 3.86/0.99  --sup_prop_simpl_new                    true
% 3.86/0.99  --sup_prop_simpl_given                  true
% 3.86/0.99  --sup_fun_splitting                     true
% 3.86/0.99  --sup_smt_interval                      50000
% 3.86/0.99  
% 3.86/0.99  ------ Superposition Simplification Setup
% 3.86/0.99  
% 3.86/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.86/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.86/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.86/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.86/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.86/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.86/0.99  --sup_immed_triv                        [TrivRules]
% 3.86/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.86/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.86/0.99  --sup_immed_bw_main                     []
% 3.86/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.86/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.86/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.86/0.99  --sup_input_bw                          []
% 3.86/0.99  
% 3.86/0.99  ------ Combination Options
% 3.86/0.99  
% 3.86/0.99  --comb_res_mult                         3
% 3.86/0.99  --comb_sup_mult                         2
% 3.86/0.99  --comb_inst_mult                        10
% 3.86/0.99  
% 3.86/0.99  ------ Debug Options
% 3.86/0.99  
% 3.86/0.99  --dbg_backtrace                         false
% 3.86/0.99  --dbg_dump_prop_clauses                 false
% 3.86/0.99  --dbg_dump_prop_clauses_file            -
% 3.86/0.99  --dbg_out_stat                          false
% 3.86/0.99  ------ Parsing...
% 3.86/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.86/0.99  ------ Proving...
% 3.86/0.99  ------ Problem Properties 
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  clauses                                 27
% 3.86/0.99  conjectures                             4
% 3.86/0.99  EPR                                     8
% 3.86/0.99  Horn                                    25
% 3.86/0.99  unary                                   7
% 3.86/0.99  binary                                  6
% 3.86/0.99  lits                                    68
% 3.86/0.99  lits eq                                 23
% 3.86/0.99  fd_pure                                 0
% 3.86/0.99  fd_pseudo                               0
% 3.86/0.99  fd_cond                                 1
% 3.86/0.99  fd_pseudo_cond                          1
% 3.86/0.99  AC symbols                              0
% 3.86/0.99  
% 3.86/0.99  ------ Schedule dynamic 5 is on 
% 3.86/0.99  
% 3.86/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  ------ 
% 3.86/0.99  Current options:
% 3.86/0.99  ------ 
% 3.86/0.99  
% 3.86/0.99  ------ Input Options
% 3.86/0.99  
% 3.86/0.99  --out_options                           all
% 3.86/0.99  --tptp_safe_out                         true
% 3.86/0.99  --problem_path                          ""
% 3.86/0.99  --include_path                          ""
% 3.86/0.99  --clausifier                            res/vclausify_rel
% 3.86/0.99  --clausifier_options                    ""
% 3.86/0.99  --stdin                                 false
% 3.86/0.99  --stats_out                             all
% 3.86/0.99  
% 3.86/0.99  ------ General Options
% 3.86/0.99  
% 3.86/0.99  --fof                                   false
% 3.86/0.99  --time_out_real                         305.
% 3.86/0.99  --time_out_virtual                      -1.
% 3.86/0.99  --symbol_type_check                     false
% 3.86/0.99  --clausify_out                          false
% 3.86/0.99  --sig_cnt_out                           false
% 3.86/0.99  --trig_cnt_out                          false
% 3.86/0.99  --trig_cnt_out_tolerance                1.
% 3.86/0.99  --trig_cnt_out_sk_spl                   false
% 3.86/0.99  --abstr_cl_out                          false
% 3.86/0.99  
% 3.86/0.99  ------ Global Options
% 3.86/0.99  
% 3.86/0.99  --schedule                              default
% 3.86/0.99  --add_important_lit                     false
% 3.86/0.99  --prop_solver_per_cl                    1000
% 3.86/0.99  --min_unsat_core                        false
% 3.86/0.99  --soft_assumptions                      false
% 3.86/0.99  --soft_lemma_size                       3
% 3.86/0.99  --prop_impl_unit_size                   0
% 3.86/0.99  --prop_impl_unit                        []
% 3.86/0.99  --share_sel_clauses                     true
% 3.86/0.99  --reset_solvers                         false
% 3.86/0.99  --bc_imp_inh                            [conj_cone]
% 3.86/0.99  --conj_cone_tolerance                   3.
% 3.86/0.99  --extra_neg_conj                        none
% 3.86/0.99  --large_theory_mode                     true
% 3.86/0.99  --prolific_symb_bound                   200
% 3.86/0.99  --lt_threshold                          2000
% 3.86/0.99  --clause_weak_htbl                      true
% 3.86/0.99  --gc_record_bc_elim                     false
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing Options
% 3.86/0.99  
% 3.86/0.99  --preprocessing_flag                    true
% 3.86/0.99  --time_out_prep_mult                    0.1
% 3.86/0.99  --splitting_mode                        input
% 3.86/0.99  --splitting_grd                         true
% 3.86/0.99  --splitting_cvd                         false
% 3.86/0.99  --splitting_cvd_svl                     false
% 3.86/0.99  --splitting_nvd                         32
% 3.86/0.99  --sub_typing                            true
% 3.86/0.99  --prep_gs_sim                           true
% 3.86/0.99  --prep_unflatten                        true
% 3.86/0.99  --prep_res_sim                          true
% 3.86/0.99  --prep_upred                            true
% 3.86/0.99  --prep_sem_filter                       exhaustive
% 3.86/0.99  --prep_sem_filter_out                   false
% 3.86/0.99  --pred_elim                             true
% 3.86/0.99  --res_sim_input                         true
% 3.86/0.99  --eq_ax_congr_red                       true
% 3.86/0.99  --pure_diseq_elim                       true
% 3.86/0.99  --brand_transform                       false
% 3.86/0.99  --non_eq_to_eq                          false
% 3.86/0.99  --prep_def_merge                        true
% 3.86/0.99  --prep_def_merge_prop_impl              false
% 3.86/0.99  --prep_def_merge_mbd                    true
% 3.86/0.99  --prep_def_merge_tr_red                 false
% 3.86/0.99  --prep_def_merge_tr_cl                  false
% 3.86/0.99  --smt_preprocessing                     true
% 3.86/0.99  --smt_ac_axioms                         fast
% 3.86/0.99  --preprocessed_out                      false
% 3.86/0.99  --preprocessed_stats                    false
% 3.86/0.99  
% 3.86/0.99  ------ Abstraction refinement Options
% 3.86/0.99  
% 3.86/0.99  --abstr_ref                             []
% 3.86/0.99  --abstr_ref_prep                        false
% 3.86/0.99  --abstr_ref_until_sat                   false
% 3.86/0.99  --abstr_ref_sig_restrict                funpre
% 3.86/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.86/0.99  --abstr_ref_under                       []
% 3.86/0.99  
% 3.86/0.99  ------ SAT Options
% 3.86/0.99  
% 3.86/0.99  --sat_mode                              false
% 3.86/0.99  --sat_fm_restart_options                ""
% 3.86/0.99  --sat_gr_def                            false
% 3.86/0.99  --sat_epr_types                         true
% 3.86/0.99  --sat_non_cyclic_types                  false
% 3.86/0.99  --sat_finite_models                     false
% 3.86/0.99  --sat_fm_lemmas                         false
% 3.86/0.99  --sat_fm_prep                           false
% 3.86/0.99  --sat_fm_uc_incr                        true
% 3.86/0.99  --sat_out_model                         small
% 3.86/0.99  --sat_out_clauses                       false
% 3.86/0.99  
% 3.86/0.99  ------ QBF Options
% 3.86/0.99  
% 3.86/0.99  --qbf_mode                              false
% 3.86/0.99  --qbf_elim_univ                         false
% 3.86/0.99  --qbf_dom_inst                          none
% 3.86/0.99  --qbf_dom_pre_inst                      false
% 3.86/0.99  --qbf_sk_in                             false
% 3.86/0.99  --qbf_pred_elim                         true
% 3.86/0.99  --qbf_split                             512
% 3.86/0.99  
% 3.86/0.99  ------ BMC1 Options
% 3.86/0.99  
% 3.86/0.99  --bmc1_incremental                      false
% 3.86/0.99  --bmc1_axioms                           reachable_all
% 3.86/0.99  --bmc1_min_bound                        0
% 3.86/0.99  --bmc1_max_bound                        -1
% 3.86/0.99  --bmc1_max_bound_default                -1
% 3.86/0.99  --bmc1_symbol_reachability              true
% 3.86/0.99  --bmc1_property_lemmas                  false
% 3.86/0.99  --bmc1_k_induction                      false
% 3.86/0.99  --bmc1_non_equiv_states                 false
% 3.86/0.99  --bmc1_deadlock                         false
% 3.86/0.99  --bmc1_ucm                              false
% 3.86/0.99  --bmc1_add_unsat_core                   none
% 3.86/0.99  --bmc1_unsat_core_children              false
% 3.86/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.86/0.99  --bmc1_out_stat                         full
% 3.86/0.99  --bmc1_ground_init                      false
% 3.86/0.99  --bmc1_pre_inst_next_state              false
% 3.86/0.99  --bmc1_pre_inst_state                   false
% 3.86/0.99  --bmc1_pre_inst_reach_state             false
% 3.86/0.99  --bmc1_out_unsat_core                   false
% 3.86/0.99  --bmc1_aig_witness_out                  false
% 3.86/0.99  --bmc1_verbose                          false
% 3.86/0.99  --bmc1_dump_clauses_tptp                false
% 3.86/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.86/0.99  --bmc1_dump_file                        -
% 3.86/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.86/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.86/0.99  --bmc1_ucm_extend_mode                  1
% 3.86/0.99  --bmc1_ucm_init_mode                    2
% 3.86/0.99  --bmc1_ucm_cone_mode                    none
% 3.86/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.86/0.99  --bmc1_ucm_relax_model                  4
% 3.86/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.86/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.86/0.99  --bmc1_ucm_layered_model                none
% 3.86/0.99  --bmc1_ucm_max_lemma_size               10
% 3.86/0.99  
% 3.86/0.99  ------ AIG Options
% 3.86/0.99  
% 3.86/0.99  --aig_mode                              false
% 3.86/0.99  
% 3.86/0.99  ------ Instantiation Options
% 3.86/0.99  
% 3.86/0.99  --instantiation_flag                    true
% 3.86/0.99  --inst_sos_flag                         true
% 3.86/0.99  --inst_sos_phase                        true
% 3.86/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.86/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.86/0.99  --inst_lit_sel_side                     none
% 3.86/0.99  --inst_solver_per_active                1400
% 3.86/0.99  --inst_solver_calls_frac                1.
% 3.86/0.99  --inst_passive_queue_type               priority_queues
% 3.86/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.86/0.99  --inst_passive_queues_freq              [25;2]
% 3.86/0.99  --inst_dismatching                      true
% 3.86/0.99  --inst_eager_unprocessed_to_passive     true
% 3.86/0.99  --inst_prop_sim_given                   true
% 3.86/0.99  --inst_prop_sim_new                     false
% 3.86/0.99  --inst_subs_new                         false
% 3.86/0.99  --inst_eq_res_simp                      false
% 3.86/0.99  --inst_subs_given                       false
% 3.86/0.99  --inst_orphan_elimination               true
% 3.86/0.99  --inst_learning_loop_flag               true
% 3.86/0.99  --inst_learning_start                   3000
% 3.86/0.99  --inst_learning_factor                  2
% 3.86/0.99  --inst_start_prop_sim_after_learn       3
% 3.86/0.99  --inst_sel_renew                        solver
% 3.86/0.99  --inst_lit_activity_flag                true
% 3.86/0.99  --inst_restr_to_given                   false
% 3.86/0.99  --inst_activity_threshold               500
% 3.86/0.99  --inst_out_proof                        true
% 3.86/0.99  
% 3.86/0.99  ------ Resolution Options
% 3.86/0.99  
% 3.86/0.99  --resolution_flag                       false
% 3.86/0.99  --res_lit_sel                           adaptive
% 3.86/0.99  --res_lit_sel_side                      none
% 3.86/0.99  --res_ordering                          kbo
% 3.86/0.99  --res_to_prop_solver                    active
% 3.86/0.99  --res_prop_simpl_new                    false
% 3.86/0.99  --res_prop_simpl_given                  true
% 3.86/0.99  --res_passive_queue_type                priority_queues
% 3.86/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.86/0.99  --res_passive_queues_freq               [15;5]
% 3.86/0.99  --res_forward_subs                      full
% 3.86/0.99  --res_backward_subs                     full
% 3.86/0.99  --res_forward_subs_resolution           true
% 3.86/0.99  --res_backward_subs_resolution          true
% 3.86/0.99  --res_orphan_elimination                true
% 3.86/0.99  --res_time_limit                        2.
% 3.86/0.99  --res_out_proof                         true
% 3.86/0.99  
% 3.86/0.99  ------ Superposition Options
% 3.86/0.99  
% 3.86/0.99  --superposition_flag                    true
% 3.86/0.99  --sup_passive_queue_type                priority_queues
% 3.86/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.86/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.86/0.99  --demod_completeness_check              fast
% 3.86/0.99  --demod_use_ground                      true
% 3.86/0.99  --sup_to_prop_solver                    passive
% 3.86/0.99  --sup_prop_simpl_new                    true
% 3.86/0.99  --sup_prop_simpl_given                  true
% 3.86/0.99  --sup_fun_splitting                     true
% 3.86/0.99  --sup_smt_interval                      50000
% 3.86/0.99  
% 3.86/0.99  ------ Superposition Simplification Setup
% 3.86/0.99  
% 3.86/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.86/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.86/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.86/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.86/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.86/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.86/0.99  --sup_immed_triv                        [TrivRules]
% 3.86/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.86/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.86/0.99  --sup_immed_bw_main                     []
% 3.86/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.86/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.86/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.86/0.99  --sup_input_bw                          []
% 3.86/0.99  
% 3.86/0.99  ------ Combination Options
% 3.86/0.99  
% 3.86/0.99  --comb_res_mult                         3
% 3.86/0.99  --comb_sup_mult                         2
% 3.86/0.99  --comb_inst_mult                        10
% 3.86/0.99  
% 3.86/0.99  ------ Debug Options
% 3.86/0.99  
% 3.86/0.99  --dbg_backtrace                         false
% 3.86/0.99  --dbg_dump_prop_clauses                 false
% 3.86/0.99  --dbg_dump_prop_clauses_file            -
% 3.86/0.99  --dbg_out_stat                          false
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  ------ Proving...
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  % SZS status Theorem for theBenchmark.p
% 3.86/0.99  
% 3.86/0.99   Resolution empty clause
% 3.86/0.99  
% 3.86/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  fof(f3,axiom,(
% 3.86/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f39,plain,(
% 3.86/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.86/0.99    inference(nnf_transformation,[],[f3])).
% 3.86/0.99  
% 3.86/0.99  fof(f40,plain,(
% 3.86/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.86/0.99    inference(flattening,[],[f39])).
% 3.86/0.99  
% 3.86/0.99  fof(f46,plain,(
% 3.86/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.86/0.99    inference(cnf_transformation,[],[f40])).
% 3.86/0.99  
% 3.86/0.99  fof(f74,plain,(
% 3.86/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.86/0.99    inference(equality_resolution,[],[f46])).
% 3.86/0.99  
% 3.86/0.99  fof(f17,conjecture,(
% 3.86/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f18,negated_conjecture,(
% 3.86/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.86/0.99    inference(negated_conjecture,[],[f17])).
% 3.86/0.99  
% 3.86/0.99  fof(f37,plain,(
% 3.86/0.99    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.86/0.99    inference(ennf_transformation,[],[f18])).
% 3.86/0.99  
% 3.86/0.99  fof(f38,plain,(
% 3.86/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.86/0.99    inference(flattening,[],[f37])).
% 3.86/0.99  
% 3.86/0.99  fof(f42,plain,(
% 3.86/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f43,plain,(
% 3.86/0.99    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f42])).
% 3.86/0.99  
% 3.86/0.99  fof(f70,plain,(
% 3.86/0.99    r1_tarski(sK2,sK0)),
% 3.86/0.99    inference(cnf_transformation,[],[f43])).
% 3.86/0.99  
% 3.86/0.99  fof(f14,axiom,(
% 3.86/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f31,plain,(
% 3.86/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/0.99    inference(ennf_transformation,[],[f14])).
% 3.86/0.99  
% 3.86/0.99  fof(f32,plain,(
% 3.86/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/0.99    inference(flattening,[],[f31])).
% 3.86/0.99  
% 3.86/0.99  fof(f41,plain,(
% 3.86/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/0.99    inference(nnf_transformation,[],[f32])).
% 3.86/0.99  
% 3.86/0.99  fof(f58,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.86/0.99    inference(cnf_transformation,[],[f41])).
% 3.86/0.99  
% 3.86/0.99  fof(f68,plain,(
% 3.86/0.99    v1_funct_2(sK3,sK0,sK1)),
% 3.86/0.99    inference(cnf_transformation,[],[f43])).
% 3.86/0.99  
% 3.86/0.99  fof(f69,plain,(
% 3.86/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.86/0.99    inference(cnf_transformation,[],[f43])).
% 3.86/0.99  
% 3.86/0.99  fof(f11,axiom,(
% 3.86/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f26,plain,(
% 3.86/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/0.99    inference(ennf_transformation,[],[f11])).
% 3.86/0.99  
% 3.86/0.99  fof(f55,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.86/0.99    inference(cnf_transformation,[],[f26])).
% 3.86/0.99  
% 3.86/0.99  fof(f8,axiom,(
% 3.86/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f22,plain,(
% 3.86/0.99    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.86/0.99    inference(ennf_transformation,[],[f8])).
% 3.86/0.99  
% 3.86/0.99  fof(f23,plain,(
% 3.86/0.99    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.86/0.99    inference(flattening,[],[f22])).
% 3.86/0.99  
% 3.86/0.99  fof(f52,plain,(
% 3.86/0.99    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f23])).
% 3.86/0.99  
% 3.86/0.99  fof(f9,axiom,(
% 3.86/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f24,plain,(
% 3.86/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/0.99    inference(ennf_transformation,[],[f9])).
% 3.86/0.99  
% 3.86/0.99  fof(f53,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.86/0.99    inference(cnf_transformation,[],[f24])).
% 3.86/0.99  
% 3.86/0.99  fof(f13,axiom,(
% 3.86/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f29,plain,(
% 3.86/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.86/0.99    inference(ennf_transformation,[],[f13])).
% 3.86/0.99  
% 3.86/0.99  fof(f30,plain,(
% 3.86/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.86/0.99    inference(flattening,[],[f29])).
% 3.86/0.99  
% 3.86/0.99  fof(f57,plain,(
% 3.86/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 3.86/0.99    inference(cnf_transformation,[],[f30])).
% 3.86/0.99  
% 3.86/0.99  fof(f12,axiom,(
% 3.86/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f27,plain,(
% 3.86/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.86/0.99    inference(ennf_transformation,[],[f12])).
% 3.86/0.99  
% 3.86/0.99  fof(f28,plain,(
% 3.86/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.86/0.99    inference(flattening,[],[f27])).
% 3.86/0.99  
% 3.86/0.99  fof(f56,plain,(
% 3.86/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 3.86/0.99    inference(cnf_transformation,[],[f28])).
% 3.86/0.99  
% 3.86/0.99  fof(f1,axiom,(
% 3.86/0.99    v1_xboole_0(k1_xboole_0)),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f44,plain,(
% 3.86/0.99    v1_xboole_0(k1_xboole_0)),
% 3.86/0.99    inference(cnf_transformation,[],[f1])).
% 3.86/0.99  
% 3.86/0.99  fof(f62,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.86/0.99    inference(cnf_transformation,[],[f41])).
% 3.86/0.99  
% 3.86/0.99  fof(f77,plain,(
% 3.86/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.86/0.99    inference(equality_resolution,[],[f62])).
% 3.86/0.99  
% 3.86/0.99  fof(f71,plain,(
% 3.86/0.99    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.86/0.99    inference(cnf_transformation,[],[f43])).
% 3.86/0.99  
% 3.86/0.99  fof(f4,axiom,(
% 3.86/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f49,plain,(
% 3.86/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f4])).
% 3.86/0.99  
% 3.86/0.99  fof(f48,plain,(
% 3.86/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f40])).
% 3.86/0.99  
% 3.86/0.99  fof(f7,axiom,(
% 3.86/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f21,plain,(
% 3.86/0.99    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 3.86/0.99    inference(ennf_transformation,[],[f7])).
% 3.86/0.99  
% 3.86/0.99  fof(f51,plain,(
% 3.86/0.99    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f21])).
% 3.86/0.99  
% 3.86/0.99  fof(f10,axiom,(
% 3.86/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f25,plain,(
% 3.86/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.86/0.99    inference(ennf_transformation,[],[f10])).
% 3.86/0.99  
% 3.86/0.99  fof(f54,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f25])).
% 3.86/0.99  
% 3.86/0.99  fof(f67,plain,(
% 3.86/0.99    v1_funct_1(sK3)),
% 3.86/0.99    inference(cnf_transformation,[],[f43])).
% 3.86/0.99  
% 3.86/0.99  fof(f2,axiom,(
% 3.86/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f20,plain,(
% 3.86/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.86/0.99    inference(ennf_transformation,[],[f2])).
% 3.86/0.99  
% 3.86/0.99  fof(f45,plain,(
% 3.86/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f20])).
% 3.86/0.99  
% 3.86/0.99  fof(f72,plain,(
% 3.86/0.99    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.86/0.99    inference(cnf_transformation,[],[f43])).
% 3.86/0.99  
% 3.86/0.99  fof(f15,axiom,(
% 3.86/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f33,plain,(
% 3.86/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.86/0.99    inference(ennf_transformation,[],[f15])).
% 3.86/0.99  
% 3.86/0.99  fof(f34,plain,(
% 3.86/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.86/0.99    inference(flattening,[],[f33])).
% 3.86/0.99  
% 3.86/0.99  fof(f64,plain,(
% 3.86/0.99    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f34])).
% 3.86/0.99  
% 3.86/0.99  fof(f5,axiom,(
% 3.86/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f50,plain,(
% 3.86/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.86/0.99    inference(cnf_transformation,[],[f5])).
% 3.86/0.99  
% 3.86/0.99  fof(f16,axiom,(
% 3.86/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f35,plain,(
% 3.86/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.86/0.99    inference(ennf_transformation,[],[f16])).
% 3.86/0.99  
% 3.86/0.99  fof(f36,plain,(
% 3.86/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.86/0.99    inference(flattening,[],[f35])).
% 3.86/0.99  
% 3.86/0.99  fof(f66,plain,(
% 3.86/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f36])).
% 3.86/0.99  
% 3.86/0.99  fof(f63,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.86/0.99    inference(cnf_transformation,[],[f41])).
% 3.86/0.99  
% 3.86/0.99  fof(f75,plain,(
% 3.86/0.99    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.86/0.99    inference(equality_resolution,[],[f63])).
% 3.86/0.99  
% 3.86/0.99  fof(f76,plain,(
% 3.86/0.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.86/0.99    inference(equality_resolution,[],[f75])).
% 3.86/0.99  
% 3.86/0.99  fof(f65,plain,(
% 3.86/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f34])).
% 3.86/0.99  
% 3.86/0.99  fof(f60,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.86/0.99    inference(cnf_transformation,[],[f41])).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f74]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1124,plain,
% 3.86/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_25,negated_conjecture,
% 3.86/0.99      ( r1_tarski(sK2,sK0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1111,plain,
% 3.86/0.99      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_19,plain,
% 3.86/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.86/0.99      | k1_xboole_0 = X2 ),
% 3.86/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_27,negated_conjecture,
% 3.86/0.99      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_433,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.86/0.99      | sK3 != X0
% 3.86/0.99      | sK1 != X2
% 3.86/0.99      | sK0 != X1
% 3.86/0.99      | k1_xboole_0 = X2 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_434,plain,
% 3.86/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.86/0.99      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.86/0.99      | k1_xboole_0 = sK1 ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_433]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_26,negated_conjecture,
% 3.86/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.86/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_436,plain,
% 3.86/0.99      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.86/0.99      inference(global_propositional_subsumption,[status(thm)],[c_434,c_26]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1110,plain,
% 3.86/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_11,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1117,plain,
% 3.86/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.86/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1666,plain,
% 3.86/0.99      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1110,c_1117]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1738,plain,
% 3.86/0.99      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_436,c_1666]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.86/0.99      | ~ v1_relat_1(X1)
% 3.86/0.99      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.86/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1120,plain,
% 3.86/0.99      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.86/0.99      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1839,plain,
% 3.86/0.99      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.86/0.99      | sK1 = k1_xboole_0
% 3.86/0.99      | r1_tarski(X0,sK0) != iProver_top
% 3.86/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1738,c_1120]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1119,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.86/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1512,plain,
% 3.86/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1110,c_1119]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1936,plain,
% 3.86/0.99      ( r1_tarski(X0,sK0) != iProver_top
% 3.86/0.99      | sK1 = k1_xboole_0
% 3.86/0.99      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.86/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1839,c_1512]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1937,plain,
% 3.86/0.99      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.86/0.99      | sK1 = k1_xboole_0
% 3.86/0.99      | r1_tarski(X0,sK0) != iProver_top ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_1936]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1945,plain,
% 3.86/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1111,c_1937]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_13,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | ~ r1_tarski(X3,X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1115,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.86/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.86/0.99      | r1_tarski(X3,X0) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2299,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.86/0.99      | r1_tarski(X0,sK3) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1110,c_1115]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_12,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.86/0.99      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 3.86/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1116,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.86/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2500,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 3.86/0.99      | r1_tarski(X0,sK3) != iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_2299,c_1116]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4593,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 3.86/0.99      | r1_tarski(X0,X2) != iProver_top
% 3.86/0.99      | r1_tarski(X2,sK3) != iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(X2),X1) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_2500,c_1115]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_12726,plain,
% 3.86/0.99      ( sK1 = k1_xboole_0
% 3.86/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 3.86/0.99      | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
% 3.86/0.99      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 3.86/0.99      | r1_tarski(sK2,X1) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1945,c_4593]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_0,plain,
% 3.86/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_90,plain,
% 3.86/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_691,plain,( X0 = X0 ),theory(equality) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1252,plain,
% 3.86/0.99      ( sK0 = sK0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_691]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_694,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.86/0.99      theory(equality) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1185,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,X1)
% 3.86/0.99      | r1_tarski(sK0,k1_xboole_0)
% 3.86/0.99      | sK0 != X0
% 3.86/0.99      | k1_xboole_0 != X1 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_694]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1244,plain,
% 3.86/0.99      ( ~ r1_tarski(sK0,X0)
% 3.86/0.99      | r1_tarski(sK0,k1_xboole_0)
% 3.86/0.99      | sK0 != sK0
% 3.86/0.99      | k1_xboole_0 != X0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1185]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1361,plain,
% 3.86/0.99      ( ~ r1_tarski(sK0,sK0)
% 3.86/0.99      | r1_tarski(sK0,k1_xboole_0)
% 3.86/0.99      | sK0 != sK0
% 3.86/0.99      | k1_xboole_0 != sK0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1244]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1362,plain,
% 3.86/0.99      ( sK0 != sK0
% 3.86/0.99      | k1_xboole_0 != sK0
% 3.86/0.99      | r1_tarski(sK0,sK0) != iProver_top
% 3.86/0.99      | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1361]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_15,plain,
% 3.86/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.86/0.99      | k1_xboole_0 = X1
% 3.86/0.99      | k1_xboole_0 = X0 ),
% 3.86/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_365,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.86/0.99      | sK3 != X0
% 3.86/0.99      | sK1 != k1_xboole_0
% 3.86/0.99      | sK0 != X1
% 3.86/0.99      | k1_xboole_0 = X0
% 3.86/0.99      | k1_xboole_0 = X1 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_366,plain,
% 3.86/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 3.86/0.99      | sK1 != k1_xboole_0
% 3.86/0.99      | k1_xboole_0 = sK3
% 3.86/0.99      | k1_xboole_0 = sK0 ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_365]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1107,plain,
% 3.86/0.99      ( sK1 != k1_xboole_0
% 3.86/0.99      | k1_xboole_0 = sK3
% 3.86/0.99      | k1_xboole_0 = sK0
% 3.86/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_24,negated_conjecture,
% 3.86/0.99      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.86/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5,plain,
% 3.86/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_80,plain,
% 3.86/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.86/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_85,plain,
% 3.86/0.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_692,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1322,plain,
% 3.86/0.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_692]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1323,plain,
% 3.86/0.99      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1322]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1472,plain,
% 3.86/0.99      ( k1_xboole_0 = sK0 | sK1 != k1_xboole_0 ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_1107,c_24,c_80,c_85,c_1323]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1473,plain,
% 3.86/0.99      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK0 ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_1472]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5844,plain,
% 3.86/0.99      ( r1_tarski(sK0,sK0) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5845,plain,
% 3.86/0.99      ( r1_tarski(sK0,sK0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_5844]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7,plain,
% 3.86/0.99      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4324,plain,
% 3.86/0.99      ( r1_tarski(k7_relat_1(sK3,X0),sK3) | ~ v1_relat_1(sK3) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9000,plain,
% 3.86/0.99      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) | ~ v1_relat_1(sK3) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_4324]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9003,plain,
% 3.86/0.99      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) = iProver_top
% 3.86/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_9000]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2347,plain,
% 3.86/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1110,c_1116]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2650,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 3.86/0.99      | r1_tarski(X0,sK3) != iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK3),X1) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_2347,c_1115]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_10,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | ~ v1_xboole_0(X1)
% 3.86/0.99      | v1_xboole_0(X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1118,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.86/0.99      | v1_xboole_0(X1) != iProver_top
% 3.86/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5035,plain,
% 3.86/0.99      ( r1_tarski(X0,sK3) != iProver_top
% 3.86/0.99      | r1_tarski(k1_relat_1(sK3),X1) != iProver_top
% 3.86/0.99      | v1_xboole_0(X1) != iProver_top
% 3.86/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_2650,c_1118]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9281,plain,
% 3.86/0.99      ( sK1 = k1_xboole_0
% 3.86/0.99      | r1_tarski(X0,sK3) != iProver_top
% 3.86/0.99      | r1_tarski(sK0,X1) != iProver_top
% 3.86/0.99      | v1_xboole_0(X1) != iProver_top
% 3.86/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1738,c_5035]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1169,plain,
% 3.86/0.99      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_692]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1201,plain,
% 3.86/0.99      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1169]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2502,plain,
% 3.86/0.99      ( r1_tarski(X0,sK3) != iProver_top
% 3.86/0.99      | v1_xboole_0(X0) = iProver_top
% 3.86/0.99      | v1_xboole_0(sK0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_2299,c_1118]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_693,plain,
% 3.86/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.86/0.99      theory(equality) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6464,plain,
% 3.86/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK0) | sK0 != X0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_693]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6465,plain,
% 3.86/0.99      ( sK0 != X0
% 3.86/0.99      | v1_xboole_0(X0) != iProver_top
% 3.86/0.99      | v1_xboole_0(sK0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_6464]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6467,plain,
% 3.86/0.99      ( sK0 != k1_xboole_0
% 3.86/0.99      | v1_xboole_0(sK0) = iProver_top
% 3.86/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_6465]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9285,plain,
% 3.86/0.99      ( r1_tarski(X0,sK3) != iProver_top
% 3.86/0.99      | r1_tarski(sK0,X1) != iProver_top
% 3.86/0.99      | v1_xboole_0(X1) != iProver_top
% 3.86/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_9281,c_90,c_1201,c_1252,c_1473,c_2502,c_6467]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9289,plain,
% 3.86/0.99      ( r1_tarski(sK0,X0) != iProver_top
% 3.86/0.99      | v1_xboole_0(X0) != iProver_top
% 3.86/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1124,c_9285]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_28,negated_conjecture,
% 3.86/0.99      ( v1_funct_1(sK3) ),
% 3.86/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_79,plain,
% 3.86/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_81,plain,
% 3.86/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_79]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1,plain,
% 3.86/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.86/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_87,plain,
% 3.86/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_23,negated_conjecture,
% 3.86/0.99      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.86/0.99      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.86/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.86/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_444,plain,
% 3.86/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.86/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.86/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 3.86/0.99      | sK2 != sK0
% 3.86/0.99      | sK1 != sK1 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1162,plain,
% 3.86/0.99      ( ~ r1_tarski(sK2,k1_xboole_0)
% 3.86/0.99      | ~ r1_tarski(k1_xboole_0,sK2)
% 3.86/0.99      | sK2 = k1_xboole_0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1178,plain,
% 3.86/0.99      ( sK2 != X0 | sK2 = sK0 | sK0 != X0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_692]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1179,plain,
% 3.86/0.99      ( sK2 = sK0 | sK2 != k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1178]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1214,plain,
% 3.86/0.99      ( sK2 = sK2 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_691]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1245,plain,
% 3.86/0.99      ( sK0 != sK0
% 3.86/0.99      | k1_xboole_0 != X0
% 3.86/0.99      | r1_tarski(sK0,X0) != iProver_top
% 3.86/0.99      | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1244]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1255,plain,
% 3.86/0.99      ( sK1 = sK1 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_691]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1180,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,X1)
% 3.86/0.99      | r1_tarski(sK2,k1_xboole_0)
% 3.86/0.99      | sK2 != X0
% 3.86/0.99      | k1_xboole_0 != X1 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_694]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1239,plain,
% 3.86/0.99      ( ~ r1_tarski(sK2,X0)
% 3.86/0.99      | r1_tarski(sK2,k1_xboole_0)
% 3.86/0.99      | sK2 != sK2
% 3.86/0.99      | k1_xboole_0 != X0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1180]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1290,plain,
% 3.86/0.99      ( ~ r1_tarski(sK2,sK0)
% 3.86/0.99      | r1_tarski(sK2,k1_xboole_0)
% 3.86/0.99      | sK2 != sK2
% 3.86/0.99      | k1_xboole_0 != sK0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1239]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1308,plain,
% 3.86/0.99      ( ~ v1_xboole_0(sK0) | k1_xboole_0 = sK0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1309,plain,
% 3.86/0.99      ( k1_xboole_0 = sK0 | v1_xboole_0(sK0) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1308]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_21,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | ~ v1_funct_1(X0)
% 3.86/0.99      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.86/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1326,plain,
% 3.86/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.86/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.86/0.99      | ~ v1_funct_1(sK3) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1466,plain,
% 3.86/0.99      ( r1_tarski(k1_xboole_0,sK2) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1514,plain,
% 3.86/0.99      ( v1_relat_1(sK3) ),
% 3.86/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1512]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1671,plain,
% 3.86/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.86/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 3.86/0.99      | sK3 != X0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_692]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1672,plain,
% 3.86/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 3.86/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.86/0.99      | sK3 != k1_xboole_0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1671]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1673,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.86/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.86/0.99      | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1675,plain,
% 3.86/0.99      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.86/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.86/0.99      | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1673]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1506,plain,
% 3.86/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.86/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
% 3.86/0.99      | k1_xboole_0 != X0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_692]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1721,plain,
% 3.86/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2)
% 3.86/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
% 3.86/0.99      | k1_xboole_0 != k2_partfun1(sK0,sK1,sK3,sK2) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1506]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1894,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | ~ r1_tarski(sK0,X0) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1895,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.86/0.99      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.86/0.99      | r1_tarski(sK0,X0) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1894]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1897,plain,
% 3.86/0.99      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 3.86/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.86/0.99      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1895]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6,plain,
% 3.86/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.86/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1122,plain,
% 3.86/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2297,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.86/0.99      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1122,c_1115]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2301,plain,
% 3.86/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 3.86/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_2297]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2300,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | ~ r1_tarski(X0,k1_xboole_0) ),
% 3.86/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2297]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2302,plain,
% 3.86/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 3.86/0.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_2300]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2330,plain,
% 3.86/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2415,plain,
% 3.86/0.99      ( sK3 = sK3 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_691]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1654,plain,
% 3.86/0.99      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_692]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2630,plain,
% 3.86/0.99      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1654]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2631,plain,
% 3.86/0.99      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_2630]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2863,plain,
% 3.86/0.99      ( ~ v1_xboole_0(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.86/0.99      | k1_xboole_0 = k2_partfun1(sK0,sK1,sK3,sK2) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3682,plain,
% 3.86/0.99      ( ~ v1_xboole_0(sK3) | k1_xboole_0 = sK3 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3683,plain,
% 3.86/0.99      ( k1_xboole_0 = sK3 | v1_xboole_0(sK3) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_3682]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_22,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | ~ v1_funct_1(X0)
% 3.86/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.86/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4280,plain,
% 3.86/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.86/0.99      | ~ v1_funct_1(sK3)
% 3.86/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4285,plain,
% 3.86/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,sK2) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_691]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4658,plain,
% 3.86/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.86/0.99      | ~ v1_xboole_0(X0)
% 3.86/0.99      | v1_xboole_0(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4660,plain,
% 3.86/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 3.86/0.99      | v1_xboole_0(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.86/0.99      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_4658]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6459,plain,
% 3.86/0.99      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.86/0.99      | ~ v1_xboole_0(X0)
% 3.86/0.99      | v1_xboole_0(sK0) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6460,plain,
% 3.86/0.99      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.86/0.99      | v1_xboole_0(X0) != iProver_top
% 3.86/0.99      | v1_xboole_0(sK0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_6459]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6462,plain,
% 3.86/0.99      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.86/0.99      | v1_xboole_0(sK0) = iProver_top
% 3.86/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_6460]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3670,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,X1)
% 3.86/0.99      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X2)
% 3.86/0.99      | X2 != X1
% 3.86/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != X0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_694]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6954,plain,
% 3.86/0.99      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
% 3.86/0.99      | ~ r1_tarski(k7_relat_1(sK3,sK2),X1)
% 3.86/0.99      | X0 != X1
% 3.86/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_3670]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8319,plain,
% 3.86/0.99      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
% 3.86/0.99      | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
% 3.86/0.99      | X0 != sK3
% 3.86/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_6954]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8322,plain,
% 3.86/0.99      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
% 3.86/0.99      | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
% 3.86/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
% 3.86/0.99      | k1_xboole_0 != sK3 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_8319]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2037,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/0.99      | ~ r1_tarski(X0,k1_xboole_0) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8904,plain,
% 3.86/0.99      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.86/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.86/1.00      | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_2037]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_8910,plain,
% 3.86/1.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 3.86/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 3.86/1.00      | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_8904]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_9339,plain,
% 3.86/1.00      ( v1_xboole_0(X0) != iProver_top | r1_tarski(sK0,X0) != iProver_top ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_9289,c_28,c_26,c_25,c_80,c_81,c_87,c_0,c_90,c_444,c_1162,
% 3.86/1.00                 c_1179,c_1201,c_1214,c_1245,c_1252,c_1255,c_1290,c_1309,
% 3.86/1.00                 c_1326,c_1466,c_1514,c_1672,c_1675,c_1721,c_1897,c_2301,
% 3.86/1.00                 c_2302,c_2330,c_2415,c_2631,c_2863,c_3683,c_4280,c_4285,
% 3.86/1.00                 c_4660,c_6462,c_8322,c_8910,c_9000]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_9340,plain,
% 3.86/1.00      ( r1_tarski(sK0,X0) != iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.86/1.00      inference(renaming,[status(thm)],[c_9339]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_9342,plain,
% 3.86/1.00      ( r1_tarski(sK0,k1_xboole_0) != iProver_top
% 3.86/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_9340]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_14792,plain,
% 3.86/1.00      ( r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
% 3.86/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 3.86/1.00      | r1_tarski(sK2,X1) != iProver_top ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_12726,c_28,c_80,c_0,c_1179,c_1193,c_1201,c_1214,c_1252,
% 3.86/1.00                 c_1410,c_1473,c_1490,c_1512,c_1672,c_1712,c_1724,c_2120,
% 3.86/1.00                 c_2155,c_2302,c_2331,c_2415,c_2543,c_2631,c_2990,c_3682,
% 3.86/1.00                 c_5076,c_6312,c_6466,c_9003]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_14793,plain,
% 3.86/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 3.86/1.00      | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
% 3.86/1.00      | r1_tarski(sK2,X1) != iProver_top ),
% 3.86/1.00      inference(renaming,[status(thm)],[c_14792]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1121,plain,
% 3.86/1.00      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 3.86/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_4591,plain,
% 3.86/1.00      ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
% 3.86/1.00      | r1_tarski(X1,sK3) != iProver_top
% 3.86/1.00      | r1_tarski(k1_relat_1(X1),X0) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_2500,c_1117]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_7182,plain,
% 3.86/1.00      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 3.86/1.00      | sK1 = k1_xboole_0
% 3.86/1.00      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 3.86/1.00      | r1_tarski(sK2,X0) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1945,c_4591]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1165,plain,
% 3.86/1.00      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_692]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1193,plain,
% 3.86/1.00      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_1165]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_521,plain,
% 3.86/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.86/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.86/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 3.86/1.00      | sK2 != sK0 ),
% 3.86/1.00      inference(equality_resolution_simp,[status(thm)],[c_444]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1103,plain,
% 3.86/1.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 3.86/1.00      | sK2 != sK0
% 3.86/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.86/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_521]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_29,plain,
% 3.86/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_31,plain,
% 3.86/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_445,plain,
% 3.86/1.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 3.86/1.00      | sK2 != sK0
% 3.86/1.00      | sK1 != sK1
% 3.86/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.86/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_444]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1327,plain,
% 3.86/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.86/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 3.86/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_1326]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1409,plain,
% 3.86/1.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.86/1.00      | sK2 != sK0
% 3.86/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3 ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_1103,c_29,c_31,c_445,c_1255,c_1327]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1410,plain,
% 3.86/1.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 3.86/1.00      | sK2 != sK0
% 3.86/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.86/1.00      inference(renaming,[status(thm)],[c_1409]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_14,plain,
% 3.86/1.00      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.86/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.86/1.00      | k1_xboole_0 = X0 ),
% 3.86/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_339,plain,
% 3.86/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.86/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.86/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.86/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.86/1.00      | sK2 != X0
% 3.86/1.00      | sK1 != k1_xboole_0
% 3.86/1.00      | k1_xboole_0 = X0 ),
% 3.86/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_340,plain,
% 3.86/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.86/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.86/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.86/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.86/1.00      | sK1 != k1_xboole_0
% 3.86/1.00      | k1_xboole_0 = sK2 ),
% 3.86/1.00      inference(unflattening,[status(thm)],[c_339]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_354,plain,
% 3.86/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.86/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.86/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.86/1.00      | sK1 != k1_xboole_0
% 3.86/1.00      | k1_xboole_0 = sK2 ),
% 3.86/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_340,c_6]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1108,plain,
% 3.86/1.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.86/1.00      | sK1 != k1_xboole_0
% 3.86/1.00      | k1_xboole_0 = sK2
% 3.86/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.86/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_354]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1285,plain,
% 3.86/1.00      ( ~ r1_tarski(sK2,k1_xboole_0)
% 3.86/1.00      | ~ r1_tarski(k1_xboole_0,sK2)
% 3.86/1.00      | k1_xboole_0 = sK2 ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1490,plain,
% 3.86/1.00      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK2 ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_1108,c_25,c_1214,c_1285,c_1290,c_1466,c_1473]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1711,plain,
% 3.86/1.00      ( v1_xboole_0(sK3) = iProver_top | v1_xboole_0(sK0) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1110,c_1118]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1712,plain,
% 3.86/1.00      ( v1_xboole_0(sK3) | ~ v1_xboole_0(sK0) ),
% 3.86/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1711]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1723,plain,
% 3.86/1.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(X0,X1,X2,X3)
% 3.86/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
% 3.86/1.00      | k1_xboole_0 != k2_partfun1(X0,X1,X2,X3) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_1506]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1724,plain,
% 3.86/1.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 3.86/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
% 3.86/1.00      | k1_xboole_0 != k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_1723]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_20,plain,
% 3.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/1.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/1.00      | ~ v1_funct_1(X0) ),
% 3.86/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1114,plain,
% 3.86/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.86/1.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.86/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2112,plain,
% 3.86/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.86/1.00      | v1_funct_1(X0) != iProver_top
% 3.86/1.00      | v1_xboole_0(X1) != iProver_top
% 3.86/1.00      | v1_xboole_0(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1114,c_1118]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2118,plain,
% 3.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/1.00      | ~ v1_funct_1(X0)
% 3.86/1.00      | ~ v1_xboole_0(X1)
% 3.86/1.00      | v1_xboole_0(k2_partfun1(X1,X2,X0,X3)) ),
% 3.86/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2112]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2120,plain,
% 3.86/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 3.86/1.00      | ~ v1_funct_1(k1_xboole_0)
% 3.86/1.00      | v1_xboole_0(k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 3.86/1.00      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_2118]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_696,plain,
% 3.86/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.86/1.00      theory(equality) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1683,plain,
% 3.86/1.00      ( ~ m1_subset_1(X0,X1)
% 3.86/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.86/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.86/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != X1 ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_696]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2152,plain,
% 3.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.86/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.86/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.86/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_1683]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2153,plain,
% 3.86/1.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.86/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))
% 3.86/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.86/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_2152]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2155,plain,
% 3.86/1.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.86/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))
% 3.86/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
% 3.86/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_2153]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2331,plain,
% 3.86/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_2330]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2543,plain,
% 3.86/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_691]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2988,plain,
% 3.86/1.00      ( ~ v1_xboole_0(k2_partfun1(X0,X1,X2,X3))
% 3.86/1.00      | k1_xboole_0 = k2_partfun1(X0,X1,X2,X3) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2990,plain,
% 3.86/1.00      ( ~ v1_xboole_0(k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 3.86/1.00      | k1_xboole_0 = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_2988]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_700,plain,
% 3.86/1.00      ( X0 != X1
% 3.86/1.00      | X2 != X3
% 3.86/1.00      | X4 != X5
% 3.86/1.00      | X6 != X7
% 3.86/1.00      | k2_partfun1(X0,X2,X4,X6) = k2_partfun1(X1,X3,X5,X7) ),
% 3.86/1.00      theory(equality) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_5075,plain,
% 3.86/1.00      ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(X0,X1,X2,X3)
% 3.86/1.00      | sK2 != X3
% 3.86/1.00      | sK3 != X2
% 3.86/1.00      | sK1 != X1
% 3.86/1.00      | sK0 != X0 ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_700]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_5076,plain,
% 3.86/1.00      ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 3.86/1.00      | sK2 != k1_xboole_0
% 3.86/1.00      | sK3 != k1_xboole_0
% 3.86/1.00      | sK1 != k1_xboole_0
% 3.86/1.00      | sK0 != k1_xboole_0 ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_5075]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_701,plain,
% 3.86/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.86/1.00      theory(equality) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_6310,plain,
% 3.86/1.00      ( v1_funct_1(X0) | ~ v1_funct_1(sK3) | X0 != sK3 ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_701]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_6312,plain,
% 3.86/1.00      ( ~ v1_funct_1(sK3) | v1_funct_1(k1_xboole_0) | k1_xboole_0 != sK3 ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_6310]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_6466,plain,
% 3.86/1.00      ( v1_xboole_0(sK0) | ~ v1_xboole_0(k1_xboole_0) | sK0 != k1_xboole_0 ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_6464]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_7205,plain,
% 3.86/1.00      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 3.86/1.00      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 3.86/1.00      | r1_tarski(sK2,X0) != iProver_top ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_7182,c_28,c_80,c_0,c_1179,c_1193,c_1201,c_1214,c_1252,
% 3.86/1.00                 c_1410,c_1473,c_1490,c_1672,c_1712,c_1724,c_2120,c_2155,
% 3.86/1.00                 c_2302,c_2331,c_2415,c_2543,c_2631,c_2990,c_3682,c_5076,
% 3.86/1.00                 c_6312,c_6466]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_7211,plain,
% 3.86/1.00      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 3.86/1.00      | r1_tarski(sK2,X0) != iProver_top
% 3.86/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1121,c_7205]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_9070,plain,
% 3.86/1.00      ( r1_tarski(sK2,X0) != iProver_top
% 3.86/1.00      | k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_7211,c_1512,c_7205,c_9003]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_9071,plain,
% 3.86/1.00      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 3.86/1.00      | r1_tarski(sK2,X0) != iProver_top ),
% 3.86/1.00      inference(renaming,[status(thm)],[c_9070]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_9076,plain,
% 3.86/1.00      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1124,c_9071]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1112,plain,
% 3.86/1.00      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.86/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.86/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2286,plain,
% 3.86/1.00      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.86/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1110,c_1112]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2480,plain,
% 3.86/1.00      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.86/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2286,c_29]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_17,plain,
% 3.86/1.00      ( v1_funct_2(X0,X1,X2)
% 3.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.86/1.00      | k1_xboole_0 = X2 ),
% 3.86/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_417,plain,
% 3.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/1.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.86/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.86/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.86/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.86/1.00      | sK2 != X1
% 3.86/1.00      | sK1 != X2
% 3.86/1.00      | k1_xboole_0 = X2 ),
% 3.86/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_418,plain,
% 3.86/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.86/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.86/1.00      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.86/1.00      | k1_xboole_0 = sK1 ),
% 3.86/1.00      inference(unflattening,[status(thm)],[c_417]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1104,plain,
% 3.86/1.00      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.86/1.00      | k1_xboole_0 = sK1
% 3.86/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.86/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_419,plain,
% 3.86/1.00      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.86/1.00      | k1_xboole_0 = sK1
% 3.86/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.86/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1335,plain,
% 3.86/1.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.86/1.00      | k1_xboole_0 = sK1
% 3.86/1.00      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_1104,c_29,c_31,c_419,c_1327]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1336,plain,
% 3.86/1.00      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.86/1.00      | k1_xboole_0 = sK1
% 3.86/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.86/1.00      inference(renaming,[status(thm)],[c_1335]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2485,plain,
% 3.86/1.00      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 3.86/1.00      | sK1 = k1_xboole_0
% 3.86/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.86/1.00      inference(demodulation,[status(thm)],[c_2480,c_1336]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_9530,plain,
% 3.86/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.86/1.00      | sK1 = k1_xboole_0
% 3.86/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.86/1.00      inference(demodulation,[status(thm)],[c_9076,c_2485]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_9650,plain,
% 3.86/1.00      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_9530,c_28,c_80,c_0,c_1179,c_1193,c_1201,c_1214,c_1252,
% 3.86/1.00                 c_1410,c_1473,c_1490,c_1672,c_1712,c_1724,c_1945,c_2120,
% 3.86/1.00                 c_2155,c_2302,c_2331,c_2415,c_2543,c_2631,c_2990,c_3682,
% 3.86/1.00                 c_5076,c_6312,c_6466]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_14808,plain,
% 3.86/1.00      ( r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
% 3.86/1.00      | r1_tarski(sK2,sK2) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_14793,c_9650]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1436,plain,
% 3.86/1.00      ( r1_tarski(sK2,sK2) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1437,plain,
% 3.86/1.00      ( r1_tarski(sK2,sK2) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_1436]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_14833,plain,
% 3.86/1.00      ( r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_14808,c_1437]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_14837,plain,
% 3.86/1.00      ( $false ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1124,c_14833]) ).
% 3.86/1.00  
% 3.86/1.00  
% 3.86/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.86/1.00  
% 3.86/1.00  ------                               Statistics
% 3.86/1.00  
% 3.86/1.00  ------ General
% 3.86/1.00  
% 3.86/1.00  abstr_ref_over_cycles:                  0
% 3.86/1.00  abstr_ref_under_cycles:                 0
% 3.86/1.00  gc_basic_clause_elim:                   0
% 3.86/1.00  forced_gc_time:                         0
% 3.86/1.00  parsing_time:                           0.014
% 3.86/1.00  unif_index_cands_time:                  0.
% 3.86/1.00  unif_index_add_time:                    0.
% 3.86/1.00  orderings_time:                         0.
% 3.86/1.00  out_proof_time:                         0.019
% 3.86/1.00  total_time:                             0.436
% 3.86/1.00  num_of_symbols:                         48
% 3.86/1.00  num_of_terms:                           10217
% 3.86/1.00  
% 3.86/1.00  ------ Preprocessing
% 3.86/1.00  
% 3.86/1.00  num_of_splits:                          0
% 3.86/1.00  num_of_split_atoms:                     0
% 3.86/1.00  num_of_reused_defs:                     0
% 3.86/1.00  num_eq_ax_congr_red:                    11
% 3.86/1.00  num_of_sem_filtered_clauses:            1
% 3.86/1.00  num_of_subtypes:                        0
% 3.86/1.00  monotx_restored_types:                  0
% 3.86/1.00  sat_num_of_epr_types:                   0
% 3.86/1.00  sat_num_of_non_cyclic_types:            0
% 3.86/1.00  sat_guarded_non_collapsed_types:        0
% 3.86/1.00  num_pure_diseq_elim:                    0
% 3.86/1.00  simp_replaced_by:                       0
% 3.86/1.00  res_preprocessed:                       132
% 3.86/1.00  prep_upred:                             0
% 3.86/1.00  prep_unflattend:                        35
% 3.86/1.00  smt_new_axioms:                         0
% 3.86/1.00  pred_elim_cands:                        5
% 3.86/1.00  pred_elim:                              1
% 3.86/1.00  pred_elim_cl:                           1
% 3.86/1.00  pred_elim_cycles:                       4
% 3.86/1.00  merged_defs:                            0
% 3.86/1.00  merged_defs_ncl:                        0
% 3.86/1.00  bin_hyper_res:                          0
% 3.86/1.00  prep_cycles:                            4
% 3.86/1.00  pred_elim_time:                         0.006
% 3.86/1.00  splitting_time:                         0.
% 3.86/1.00  sem_filter_time:                        0.
% 3.86/1.00  monotx_time:                            0.
% 3.86/1.00  subtype_inf_time:                       0.
% 3.86/1.00  
% 3.86/1.00  ------ Problem properties
% 3.86/1.00  
% 3.86/1.00  clauses:                                27
% 3.86/1.00  conjectures:                            4
% 3.86/1.00  epr:                                    8
% 3.86/1.00  horn:                                   25
% 3.86/1.00  ground:                                 12
% 3.86/1.00  unary:                                  7
% 3.86/1.00  binary:                                 6
% 3.86/1.00  lits:                                   68
% 3.86/1.00  lits_eq:                                23
% 3.86/1.00  fd_pure:                                0
% 3.86/1.00  fd_pseudo:                              0
% 3.86/1.00  fd_cond:                                1
% 3.86/1.00  fd_pseudo_cond:                         1
% 3.86/1.00  ac_symbols:                             0
% 3.86/1.00  
% 3.86/1.00  ------ Propositional Solver
% 3.86/1.00  
% 3.86/1.00  prop_solver_calls:                      34
% 3.86/1.00  prop_fast_solver_calls:                 1445
% 3.86/1.00  smt_solver_calls:                       0
% 3.86/1.00  smt_fast_solver_calls:                  0
% 3.86/1.00  prop_num_of_clauses:                    6362
% 3.86/1.00  prop_preprocess_simplified:             14030
% 3.86/1.00  prop_fo_subsumed:                       89
% 3.86/1.00  prop_solver_time:                       0.
% 3.86/1.00  smt_solver_time:                        0.
% 3.86/1.00  smt_fast_solver_time:                   0.
% 3.86/1.00  prop_fast_solver_time:                  0.
% 3.86/1.00  prop_unsat_core_time:                   0.
% 3.86/1.00  
% 3.86/1.00  ------ QBF
% 3.86/1.00  
% 3.86/1.00  qbf_q_res:                              0
% 3.86/1.00  qbf_num_tautologies:                    0
% 3.86/1.00  qbf_prep_cycles:                        0
% 3.86/1.00  
% 3.86/1.00  ------ BMC1
% 3.86/1.00  
% 3.86/1.00  bmc1_current_bound:                     -1
% 3.86/1.00  bmc1_last_solved_bound:                 -1
% 3.86/1.00  bmc1_unsat_core_size:                   -1
% 3.86/1.00  bmc1_unsat_core_parents_size:           -1
% 3.86/1.00  bmc1_merge_next_fun:                    0
% 3.86/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.86/1.00  
% 3.86/1.00  ------ Instantiation
% 3.86/1.00  
% 3.86/1.00  inst_num_of_clauses:                    1731
% 3.86/1.00  inst_num_in_passive:                    877
% 3.86/1.00  inst_num_in_active:                     854
% 3.86/1.00  inst_num_in_unprocessed:                0
% 3.86/1.00  inst_num_of_loops:                      1060
% 3.86/1.00  inst_num_of_learning_restarts:          0
% 3.86/1.00  inst_num_moves_active_passive:          201
% 3.86/1.00  inst_lit_activity:                      0
% 3.86/1.00  inst_lit_activity_moves:                0
% 3.86/1.00  inst_num_tautologies:                   0
% 3.86/1.00  inst_num_prop_implied:                  0
% 3.86/1.00  inst_num_existing_simplified:           0
% 3.86/1.00  inst_num_eq_res_simplified:             0
% 3.86/1.00  inst_num_child_elim:                    0
% 3.86/1.00  inst_num_of_dismatching_blockings:      624
% 3.86/1.00  inst_num_of_non_proper_insts:           2446
% 3.86/1.00  inst_num_of_duplicates:                 0
% 3.86/1.00  inst_inst_num_from_inst_to_res:         0
% 3.86/1.00  inst_dismatching_checking_time:         0.
% 3.86/1.00  
% 3.86/1.00  ------ Resolution
% 3.86/1.00  
% 3.86/1.00  res_num_of_clauses:                     0
% 3.86/1.00  res_num_in_passive:                     0
% 3.86/1.00  res_num_in_active:                      0
% 3.86/1.00  res_num_of_loops:                       136
% 3.86/1.00  res_forward_subset_subsumed:            171
% 3.86/1.00  res_backward_subset_subsumed:           0
% 3.86/1.00  res_forward_subsumed:                   0
% 3.86/1.00  res_backward_subsumed:                  0
% 3.86/1.00  res_forward_subsumption_resolution:     1
% 3.86/1.00  res_backward_subsumption_resolution:    0
% 3.86/1.00  res_clause_to_clause_subsumption:       1090
% 3.86/1.00  res_orphan_elimination:                 0
% 3.86/1.00  res_tautology_del:                      367
% 3.86/1.00  res_num_eq_res_simplified:              1
% 3.86/1.00  res_num_sel_changes:                    0
% 3.86/1.00  res_moves_from_active_to_pass:          0
% 3.86/1.00  
% 3.86/1.00  ------ Superposition
% 3.86/1.00  
% 3.86/1.00  sup_time_total:                         0.
% 3.86/1.00  sup_time_generating:                    0.
% 3.86/1.00  sup_time_sim_full:                      0.
% 3.86/1.00  sup_time_sim_immed:                     0.
% 3.86/1.00  
% 3.86/1.00  sup_num_of_clauses:                     324
% 3.86/1.00  sup_num_in_active:                      172
% 3.86/1.00  sup_num_in_passive:                     152
% 3.86/1.00  sup_num_of_loops:                       211
% 3.86/1.00  sup_fw_superposition:                   320
% 3.86/1.00  sup_bw_superposition:                   239
% 3.86/1.00  sup_immediate_simplified:               181
% 3.86/1.00  sup_given_eliminated:                   0
% 3.86/1.00  comparisons_done:                       0
% 3.86/1.00  comparisons_avoided:                    27
% 3.86/1.00  
% 3.86/1.00  ------ Simplifications
% 3.86/1.00  
% 3.86/1.00  
% 3.86/1.00  sim_fw_subset_subsumed:                 68
% 3.86/1.00  sim_bw_subset_subsumed:                 17
% 3.86/1.00  sim_fw_subsumed:                        47
% 3.86/1.00  sim_bw_subsumed:                        23
% 3.86/1.00  sim_fw_subsumption_res:                 0
% 3.86/1.00  sim_bw_subsumption_res:                 0
% 3.86/1.00  sim_tautology_del:                      2
% 3.86/1.00  sim_eq_tautology_del:                   25
% 3.86/1.00  sim_eq_res_simp:                        0
% 3.86/1.00  sim_fw_demodulated:                     28
% 3.86/1.00  sim_bw_demodulated:                     11
% 3.86/1.00  sim_light_normalised:                   51
% 3.86/1.00  sim_joinable_taut:                      0
% 3.86/1.00  sim_joinable_simp:                      0
% 3.86/1.00  sim_ac_normalised:                      0
% 3.86/1.00  sim_smt_subsumption:                    0
% 3.86/1.00  
%------------------------------------------------------------------------------

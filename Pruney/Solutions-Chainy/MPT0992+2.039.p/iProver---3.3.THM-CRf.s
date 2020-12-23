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
% DateTime   : Thu Dec  3 12:03:54 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  230 (7802 expanded)
%              Number of clauses        :  166 (2587 expanded)
%              Number of leaves         :   18 (1444 expanded)
%              Depth                    :   28
%              Number of atoms          :  704 (44293 expanded)
%              Number of equality atoms :  442 (13223 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f39,plain,
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

fof(f40,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f39])).

fof(f66,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f64,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f36])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f74,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f73])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f47])).

fof(f67,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f55])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_979,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_407,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_409,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_407,c_25])).

cnf(c_978,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_984,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2046,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_978,c_984])).

cnf(c_2143,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_409,c_2046])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_986,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2598,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2143,c_986])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1171,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1172,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1171])).

cnf(c_2758,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2598,c_30,c_1172])).

cnf(c_2759,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2758])).

cnf(c_2768,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_979,c_2759])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_980,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3612,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_978,c_980])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1243,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2011,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1243])).

cnf(c_3729,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3612,c_27,c_25,c_2011])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_982,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3785,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3729,c_982])).

cnf(c_28,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5141,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3785,c_28,c_30])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_983,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5153,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5141,c_983])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_988,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5957,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X1)) = k1_relat_1(k7_relat_1(sK3,X1))
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5153,c_984])).

cnf(c_7234,plain,
    ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_988,c_5957])).

cnf(c_7257,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2768,c_7234])).

cnf(c_16,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_22,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X1
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_391,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_971,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_3736,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3729,c_971])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_981,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1859,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_978,c_981])).

cnf(c_1206,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1515,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1206])).

cnf(c_1516,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1515])).

cnf(c_2146,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1859,c_28,c_30,c_1516])).

cnf(c_3737,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3729,c_2146])).

cnf(c_3744,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3736,c_3737])).

cnf(c_7412,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7257,c_3744])).

cnf(c_7494,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7412,c_2768])).

cnf(c_7501,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5153,c_7494])).

cnf(c_11342,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2768,c_7501])).

cnf(c_4074,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4077,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4074])).

cnf(c_11345,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11342,c_4077])).

cnf(c_15,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_359,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_973,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1113,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_973,c_5])).

cnf(c_3733,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3729,c_1113])).

cnf(c_3773,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3733,c_3737])).

cnf(c_11383,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11345,c_3773])).

cnf(c_13,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_312,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_313,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_975,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1100,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_975,c_4])).

cnf(c_3734,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3729,c_1100])).

cnf(c_3762,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3734,c_3737])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_76,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_77,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_624,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1199,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_1415,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1199])).

cnf(c_623,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1416,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_1846,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_1847,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1846])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1891,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_625,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1356,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_2139,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1356])).

cnf(c_4079,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2139])).

cnf(c_6807,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3762,c_24,c_23,c_76,c_77,c_1415,c_1416,c_1847,c_1891,c_4079])).

cnf(c_11384,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11345,c_6807])).

cnf(c_11486,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_11384])).

cnf(c_11495,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11383,c_11486])).

cnf(c_11496,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11495])).

cnf(c_5151,plain,
    ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_5141,c_984])).

cnf(c_11394,plain,
    ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_11345,c_5151])).

cnf(c_11413,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11345,c_23])).

cnf(c_11414,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_11413])).

cnf(c_11464,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_11394,c_11414])).

cnf(c_11497,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11496,c_11464])).

cnf(c_11399,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11345,c_5141])).

cnf(c_11459,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11399,c_11414])).

cnf(c_11461,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11459,c_5])).

cnf(c_11501,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11497,c_11461])).

cnf(c_11502,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11501,c_5])).

cnf(c_11408,plain,
    ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_11345,c_2046])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_378,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_972,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_1044,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_972,c_5])).

cnf(c_11410,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11345,c_1044])).

cnf(c_11421,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11410,c_11414])).

cnf(c_11422,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11421])).

cnf(c_11412,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11345,c_978])).

cnf(c_11417,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11412,c_11414])).

cnf(c_11419,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11417,c_5])).

cnf(c_11425,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11422,c_11419])).

cnf(c_11428,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11408,c_11414,c_11425])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1331,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_partfun1(X2,X3,sK3,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X0 != k2_partfun1(X2,X3,sK3,X4)
    | X1 != k1_zfmisc_1(k2_zfmisc_1(X2,X3)) ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_1550,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_partfun1(X2,X3,sK3,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X0 != k2_partfun1(X2,X3,sK3,X4)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(k2_zfmisc_1(X2,X3)) ),
    inference(instantiation,[status(thm)],[c_1331])).

cnf(c_10432,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(X1))
    | k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1550])).

cnf(c_10433,plain,
    ( k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10432])).

cnf(c_10435,plain,
    ( k7_relat_1(sK3,k1_xboole_0) != k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10433])).

cnf(c_2083,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(sK0,sK1)
    | k2_zfmisc_1(sK0,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_6783,plain,
    ( X0 != k2_zfmisc_1(X1,X2)
    | X0 = k2_zfmisc_1(sK0,sK1)
    | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_2083])).

cnf(c_6788,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6783])).

cnf(c_4895,plain,
    ( k7_relat_1(sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_4897,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = k7_relat_1(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4895])).

cnf(c_1802,plain,
    ( X0 != X1
    | X0 = k2_partfun1(sK0,sK1,sK3,X2)
    | k2_partfun1(sK0,sK1,sK3,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_3443,plain,
    ( X0 = k2_partfun1(sK0,sK1,sK3,X1)
    | X0 != k7_relat_1(sK3,X1)
    | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
    inference(instantiation,[status(thm)],[c_1802])).

cnf(c_4894,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
    | k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | k7_relat_1(sK3,X0) != k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_3443])).

cnf(c_4896,plain,
    ( k2_partfun1(sK0,sK1,sK3,k1_xboole_0) != k7_relat_1(sK3,k1_xboole_0)
    | k7_relat_1(sK3,k1_xboole_0) = k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
    | k7_relat_1(sK3,k1_xboole_0) != k7_relat_1(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4894])).

cnf(c_626,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_4168,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(X0,X1)
    | sK1 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_4170,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | sK1 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4168])).

cnf(c_2299,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(X2,X3)
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_2300,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2299])).

cnf(c_2013,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,k1_xboole_0) = k7_relat_1(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2011])).

cnf(c_1238,plain,
    ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1520,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1238])).

cnf(c_1521,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1520])).

cnf(c_1523,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1521])).

cnf(c_1482,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_relat_1(sK3))
    | X2 != X0
    | k1_relat_1(sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_1484,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1482])).

cnf(c_628,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1462,plain,
    ( X0 != k2_zfmisc_1(sK0,sK1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_628])).

cnf(c_1467,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1462])).

cnf(c_1437,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_1200,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_1436,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1200])).

cnf(c_1248,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1250,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1248])).

cnf(c_82,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11502,c_11428,c_11342,c_10435,c_6788,c_4897,c_4896,c_4170,c_4077,c_2300,c_2013,c_1847,c_1523,c_1484,c_1467,c_1437,c_1436,c_1250,c_1171,c_82,c_77,c_76,c_23,c_30,c_25,c_28,c_27])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 12:21:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.45/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.00  
% 3.45/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.45/1.00  
% 3.45/1.00  ------  iProver source info
% 3.45/1.00  
% 3.45/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.45/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.45/1.00  git: non_committed_changes: false
% 3.45/1.00  git: last_make_outside_of_git: false
% 3.45/1.00  
% 3.45/1.00  ------ 
% 3.45/1.00  
% 3.45/1.00  ------ Input Options
% 3.45/1.00  
% 3.45/1.00  --out_options                           all
% 3.45/1.00  --tptp_safe_out                         true
% 3.45/1.00  --problem_path                          ""
% 3.45/1.00  --include_path                          ""
% 3.45/1.00  --clausifier                            res/vclausify_rel
% 3.45/1.00  --clausifier_options                    --mode clausify
% 3.45/1.00  --stdin                                 false
% 3.45/1.00  --stats_out                             all
% 3.45/1.00  
% 3.45/1.00  ------ General Options
% 3.45/1.00  
% 3.45/1.00  --fof                                   false
% 3.45/1.00  --time_out_real                         305.
% 3.45/1.00  --time_out_virtual                      -1.
% 3.45/1.00  --symbol_type_check                     false
% 3.45/1.00  --clausify_out                          false
% 3.45/1.00  --sig_cnt_out                           false
% 3.45/1.00  --trig_cnt_out                          false
% 3.45/1.00  --trig_cnt_out_tolerance                1.
% 3.45/1.00  --trig_cnt_out_sk_spl                   false
% 3.45/1.00  --abstr_cl_out                          false
% 3.45/1.00  
% 3.45/1.00  ------ Global Options
% 3.45/1.00  
% 3.45/1.00  --schedule                              default
% 3.45/1.00  --add_important_lit                     false
% 3.45/1.00  --prop_solver_per_cl                    1000
% 3.45/1.00  --min_unsat_core                        false
% 3.45/1.00  --soft_assumptions                      false
% 3.45/1.00  --soft_lemma_size                       3
% 3.45/1.00  --prop_impl_unit_size                   0
% 3.45/1.00  --prop_impl_unit                        []
% 3.45/1.00  --share_sel_clauses                     true
% 3.45/1.00  --reset_solvers                         false
% 3.45/1.00  --bc_imp_inh                            [conj_cone]
% 3.45/1.00  --conj_cone_tolerance                   3.
% 3.45/1.00  --extra_neg_conj                        none
% 3.45/1.00  --large_theory_mode                     true
% 3.45/1.00  --prolific_symb_bound                   200
% 3.45/1.00  --lt_threshold                          2000
% 3.45/1.00  --clause_weak_htbl                      true
% 3.45/1.00  --gc_record_bc_elim                     false
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing Options
% 3.45/1.00  
% 3.45/1.00  --preprocessing_flag                    true
% 3.45/1.00  --time_out_prep_mult                    0.1
% 3.45/1.00  --splitting_mode                        input
% 3.45/1.00  --splitting_grd                         true
% 3.45/1.00  --splitting_cvd                         false
% 3.45/1.00  --splitting_cvd_svl                     false
% 3.45/1.00  --splitting_nvd                         32
% 3.45/1.00  --sub_typing                            true
% 3.45/1.00  --prep_gs_sim                           true
% 3.45/1.00  --prep_unflatten                        true
% 3.45/1.00  --prep_res_sim                          true
% 3.45/1.00  --prep_upred                            true
% 3.45/1.00  --prep_sem_filter                       exhaustive
% 3.45/1.00  --prep_sem_filter_out                   false
% 3.45/1.00  --pred_elim                             true
% 3.45/1.00  --res_sim_input                         true
% 3.45/1.00  --eq_ax_congr_red                       true
% 3.45/1.00  --pure_diseq_elim                       true
% 3.45/1.00  --brand_transform                       false
% 3.45/1.00  --non_eq_to_eq                          false
% 3.45/1.00  --prep_def_merge                        true
% 3.45/1.00  --prep_def_merge_prop_impl              false
% 3.45/1.00  --prep_def_merge_mbd                    true
% 3.45/1.00  --prep_def_merge_tr_red                 false
% 3.45/1.00  --prep_def_merge_tr_cl                  false
% 3.45/1.00  --smt_preprocessing                     true
% 3.45/1.00  --smt_ac_axioms                         fast
% 3.45/1.00  --preprocessed_out                      false
% 3.45/1.00  --preprocessed_stats                    false
% 3.45/1.00  
% 3.45/1.00  ------ Abstraction refinement Options
% 3.45/1.00  
% 3.45/1.00  --abstr_ref                             []
% 3.45/1.00  --abstr_ref_prep                        false
% 3.45/1.00  --abstr_ref_until_sat                   false
% 3.45/1.00  --abstr_ref_sig_restrict                funpre
% 3.45/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/1.00  --abstr_ref_under                       []
% 3.45/1.00  
% 3.45/1.00  ------ SAT Options
% 3.45/1.00  
% 3.45/1.00  --sat_mode                              false
% 3.45/1.00  --sat_fm_restart_options                ""
% 3.45/1.00  --sat_gr_def                            false
% 3.45/1.00  --sat_epr_types                         true
% 3.45/1.00  --sat_non_cyclic_types                  false
% 3.45/1.00  --sat_finite_models                     false
% 3.45/1.00  --sat_fm_lemmas                         false
% 3.45/1.00  --sat_fm_prep                           false
% 3.45/1.00  --sat_fm_uc_incr                        true
% 3.45/1.00  --sat_out_model                         small
% 3.45/1.00  --sat_out_clauses                       false
% 3.45/1.00  
% 3.45/1.00  ------ QBF Options
% 3.45/1.00  
% 3.45/1.00  --qbf_mode                              false
% 3.45/1.00  --qbf_elim_univ                         false
% 3.45/1.00  --qbf_dom_inst                          none
% 3.45/1.00  --qbf_dom_pre_inst                      false
% 3.45/1.00  --qbf_sk_in                             false
% 3.45/1.00  --qbf_pred_elim                         true
% 3.45/1.00  --qbf_split                             512
% 3.45/1.00  
% 3.45/1.00  ------ BMC1 Options
% 3.45/1.00  
% 3.45/1.00  --bmc1_incremental                      false
% 3.45/1.00  --bmc1_axioms                           reachable_all
% 3.45/1.00  --bmc1_min_bound                        0
% 3.45/1.00  --bmc1_max_bound                        -1
% 3.45/1.00  --bmc1_max_bound_default                -1
% 3.45/1.00  --bmc1_symbol_reachability              true
% 3.45/1.00  --bmc1_property_lemmas                  false
% 3.45/1.00  --bmc1_k_induction                      false
% 3.45/1.00  --bmc1_non_equiv_states                 false
% 3.45/1.00  --bmc1_deadlock                         false
% 3.45/1.00  --bmc1_ucm                              false
% 3.45/1.00  --bmc1_add_unsat_core                   none
% 3.45/1.00  --bmc1_unsat_core_children              false
% 3.45/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/1.00  --bmc1_out_stat                         full
% 3.45/1.00  --bmc1_ground_init                      false
% 3.45/1.00  --bmc1_pre_inst_next_state              false
% 3.45/1.00  --bmc1_pre_inst_state                   false
% 3.45/1.00  --bmc1_pre_inst_reach_state             false
% 3.45/1.00  --bmc1_out_unsat_core                   false
% 3.45/1.00  --bmc1_aig_witness_out                  false
% 3.45/1.00  --bmc1_verbose                          false
% 3.45/1.00  --bmc1_dump_clauses_tptp                false
% 3.45/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.45/1.00  --bmc1_dump_file                        -
% 3.45/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.45/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.45/1.00  --bmc1_ucm_extend_mode                  1
% 3.45/1.00  --bmc1_ucm_init_mode                    2
% 3.45/1.00  --bmc1_ucm_cone_mode                    none
% 3.45/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.45/1.00  --bmc1_ucm_relax_model                  4
% 3.45/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.45/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/1.00  --bmc1_ucm_layered_model                none
% 3.45/1.00  --bmc1_ucm_max_lemma_size               10
% 3.45/1.00  
% 3.45/1.00  ------ AIG Options
% 3.45/1.00  
% 3.45/1.00  --aig_mode                              false
% 3.45/1.00  
% 3.45/1.00  ------ Instantiation Options
% 3.45/1.00  
% 3.45/1.00  --instantiation_flag                    true
% 3.45/1.00  --inst_sos_flag                         false
% 3.45/1.00  --inst_sos_phase                        true
% 3.45/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/1.00  --inst_lit_sel_side                     num_symb
% 3.45/1.00  --inst_solver_per_active                1400
% 3.45/1.00  --inst_solver_calls_frac                1.
% 3.45/1.00  --inst_passive_queue_type               priority_queues
% 3.45/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/1.00  --inst_passive_queues_freq              [25;2]
% 3.45/1.00  --inst_dismatching                      true
% 3.45/1.00  --inst_eager_unprocessed_to_passive     true
% 3.45/1.00  --inst_prop_sim_given                   true
% 3.45/1.00  --inst_prop_sim_new                     false
% 3.45/1.00  --inst_subs_new                         false
% 3.45/1.00  --inst_eq_res_simp                      false
% 3.45/1.00  --inst_subs_given                       false
% 3.45/1.00  --inst_orphan_elimination               true
% 3.45/1.00  --inst_learning_loop_flag               true
% 3.45/1.00  --inst_learning_start                   3000
% 3.45/1.00  --inst_learning_factor                  2
% 3.45/1.00  --inst_start_prop_sim_after_learn       3
% 3.45/1.00  --inst_sel_renew                        solver
% 3.45/1.00  --inst_lit_activity_flag                true
% 3.45/1.00  --inst_restr_to_given                   false
% 3.45/1.00  --inst_activity_threshold               500
% 3.45/1.00  --inst_out_proof                        true
% 3.45/1.00  
% 3.45/1.00  ------ Resolution Options
% 3.45/1.00  
% 3.45/1.00  --resolution_flag                       true
% 3.45/1.00  --res_lit_sel                           adaptive
% 3.45/1.00  --res_lit_sel_side                      none
% 3.45/1.00  --res_ordering                          kbo
% 3.45/1.00  --res_to_prop_solver                    active
% 3.45/1.00  --res_prop_simpl_new                    false
% 3.45/1.00  --res_prop_simpl_given                  true
% 3.45/1.00  --res_passive_queue_type                priority_queues
% 3.45/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/1.00  --res_passive_queues_freq               [15;5]
% 3.45/1.00  --res_forward_subs                      full
% 3.45/1.00  --res_backward_subs                     full
% 3.45/1.00  --res_forward_subs_resolution           true
% 3.45/1.00  --res_backward_subs_resolution          true
% 3.45/1.00  --res_orphan_elimination                true
% 3.45/1.00  --res_time_limit                        2.
% 3.45/1.00  --res_out_proof                         true
% 3.45/1.00  
% 3.45/1.00  ------ Superposition Options
% 3.45/1.00  
% 3.45/1.00  --superposition_flag                    true
% 3.45/1.00  --sup_passive_queue_type                priority_queues
% 3.45/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.45/1.00  --demod_completeness_check              fast
% 3.45/1.00  --demod_use_ground                      true
% 3.45/1.00  --sup_to_prop_solver                    passive
% 3.45/1.00  --sup_prop_simpl_new                    true
% 3.45/1.00  --sup_prop_simpl_given                  true
% 3.45/1.00  --sup_fun_splitting                     false
% 3.45/1.00  --sup_smt_interval                      50000
% 3.45/1.00  
% 3.45/1.00  ------ Superposition Simplification Setup
% 3.45/1.00  
% 3.45/1.00  --sup_indices_passive                   []
% 3.45/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_full_bw                           [BwDemod]
% 3.45/1.00  --sup_immed_triv                        [TrivRules]
% 3.45/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_immed_bw_main                     []
% 3.45/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.00  
% 3.45/1.00  ------ Combination Options
% 3.45/1.00  
% 3.45/1.00  --comb_res_mult                         3
% 3.45/1.00  --comb_sup_mult                         2
% 3.45/1.00  --comb_inst_mult                        10
% 3.45/1.00  
% 3.45/1.00  ------ Debug Options
% 3.45/1.00  
% 3.45/1.00  --dbg_backtrace                         false
% 3.45/1.00  --dbg_dump_prop_clauses                 false
% 3.45/1.00  --dbg_dump_prop_clauses_file            -
% 3.45/1.00  --dbg_out_stat                          false
% 3.45/1.00  ------ Parsing...
% 3.45/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.45/1.00  ------ Proving...
% 3.45/1.00  ------ Problem Properties 
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  clauses                                 25
% 3.45/1.00  conjectures                             4
% 3.45/1.00  EPR                                     6
% 3.45/1.00  Horn                                    22
% 3.45/1.00  unary                                   6
% 3.45/1.00  binary                                  6
% 3.45/1.00  lits                                    65
% 3.45/1.00  lits eq                                 29
% 3.45/1.00  fd_pure                                 0
% 3.45/1.00  fd_pseudo                               0
% 3.45/1.00  fd_cond                                 2
% 3.45/1.00  fd_pseudo_cond                          1
% 3.45/1.00  AC symbols                              0
% 3.45/1.00  
% 3.45/1.00  ------ Schedule dynamic 5 is on 
% 3.45/1.00  
% 3.45/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  ------ 
% 3.45/1.00  Current options:
% 3.45/1.00  ------ 
% 3.45/1.00  
% 3.45/1.00  ------ Input Options
% 3.45/1.00  
% 3.45/1.00  --out_options                           all
% 3.45/1.00  --tptp_safe_out                         true
% 3.45/1.00  --problem_path                          ""
% 3.45/1.00  --include_path                          ""
% 3.45/1.00  --clausifier                            res/vclausify_rel
% 3.45/1.00  --clausifier_options                    --mode clausify
% 3.45/1.00  --stdin                                 false
% 3.45/1.00  --stats_out                             all
% 3.45/1.00  
% 3.45/1.00  ------ General Options
% 3.45/1.00  
% 3.45/1.00  --fof                                   false
% 3.45/1.00  --time_out_real                         305.
% 3.45/1.00  --time_out_virtual                      -1.
% 3.45/1.00  --symbol_type_check                     false
% 3.45/1.00  --clausify_out                          false
% 3.45/1.00  --sig_cnt_out                           false
% 3.45/1.00  --trig_cnt_out                          false
% 3.45/1.00  --trig_cnt_out_tolerance                1.
% 3.45/1.00  --trig_cnt_out_sk_spl                   false
% 3.45/1.00  --abstr_cl_out                          false
% 3.45/1.00  
% 3.45/1.00  ------ Global Options
% 3.45/1.00  
% 3.45/1.00  --schedule                              default
% 3.45/1.00  --add_important_lit                     false
% 3.45/1.00  --prop_solver_per_cl                    1000
% 3.45/1.00  --min_unsat_core                        false
% 3.45/1.00  --soft_assumptions                      false
% 3.45/1.00  --soft_lemma_size                       3
% 3.45/1.00  --prop_impl_unit_size                   0
% 3.45/1.00  --prop_impl_unit                        []
% 3.45/1.00  --share_sel_clauses                     true
% 3.45/1.00  --reset_solvers                         false
% 3.45/1.00  --bc_imp_inh                            [conj_cone]
% 3.45/1.00  --conj_cone_tolerance                   3.
% 3.45/1.00  --extra_neg_conj                        none
% 3.45/1.00  --large_theory_mode                     true
% 3.45/1.00  --prolific_symb_bound                   200
% 3.45/1.00  --lt_threshold                          2000
% 3.45/1.00  --clause_weak_htbl                      true
% 3.45/1.00  --gc_record_bc_elim                     false
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing Options
% 3.45/1.00  
% 3.45/1.00  --preprocessing_flag                    true
% 3.45/1.00  --time_out_prep_mult                    0.1
% 3.45/1.00  --splitting_mode                        input
% 3.45/1.00  --splitting_grd                         true
% 3.45/1.00  --splitting_cvd                         false
% 3.45/1.00  --splitting_cvd_svl                     false
% 3.45/1.00  --splitting_nvd                         32
% 3.45/1.00  --sub_typing                            true
% 3.45/1.00  --prep_gs_sim                           true
% 3.45/1.00  --prep_unflatten                        true
% 3.45/1.00  --prep_res_sim                          true
% 3.45/1.00  --prep_upred                            true
% 3.45/1.00  --prep_sem_filter                       exhaustive
% 3.45/1.00  --prep_sem_filter_out                   false
% 3.45/1.00  --pred_elim                             true
% 3.45/1.00  --res_sim_input                         true
% 3.45/1.00  --eq_ax_congr_red                       true
% 3.45/1.00  --pure_diseq_elim                       true
% 3.45/1.00  --brand_transform                       false
% 3.45/1.00  --non_eq_to_eq                          false
% 3.45/1.00  --prep_def_merge                        true
% 3.45/1.00  --prep_def_merge_prop_impl              false
% 3.45/1.00  --prep_def_merge_mbd                    true
% 3.45/1.00  --prep_def_merge_tr_red                 false
% 3.45/1.00  --prep_def_merge_tr_cl                  false
% 3.45/1.00  --smt_preprocessing                     true
% 3.45/1.00  --smt_ac_axioms                         fast
% 3.45/1.00  --preprocessed_out                      false
% 3.45/1.00  --preprocessed_stats                    false
% 3.45/1.00  
% 3.45/1.00  ------ Abstraction refinement Options
% 3.45/1.00  
% 3.45/1.00  --abstr_ref                             []
% 3.45/1.00  --abstr_ref_prep                        false
% 3.45/1.00  --abstr_ref_until_sat                   false
% 3.45/1.00  --abstr_ref_sig_restrict                funpre
% 3.45/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/1.00  --abstr_ref_under                       []
% 3.45/1.00  
% 3.45/1.00  ------ SAT Options
% 3.45/1.00  
% 3.45/1.00  --sat_mode                              false
% 3.45/1.00  --sat_fm_restart_options                ""
% 3.45/1.00  --sat_gr_def                            false
% 3.45/1.00  --sat_epr_types                         true
% 3.45/1.00  --sat_non_cyclic_types                  false
% 3.45/1.00  --sat_finite_models                     false
% 3.45/1.00  --sat_fm_lemmas                         false
% 3.45/1.00  --sat_fm_prep                           false
% 3.45/1.00  --sat_fm_uc_incr                        true
% 3.45/1.00  --sat_out_model                         small
% 3.45/1.00  --sat_out_clauses                       false
% 3.45/1.00  
% 3.45/1.00  ------ QBF Options
% 3.45/1.00  
% 3.45/1.00  --qbf_mode                              false
% 3.45/1.00  --qbf_elim_univ                         false
% 3.45/1.00  --qbf_dom_inst                          none
% 3.45/1.00  --qbf_dom_pre_inst                      false
% 3.45/1.00  --qbf_sk_in                             false
% 3.45/1.00  --qbf_pred_elim                         true
% 3.45/1.00  --qbf_split                             512
% 3.45/1.00  
% 3.45/1.00  ------ BMC1 Options
% 3.45/1.00  
% 3.45/1.00  --bmc1_incremental                      false
% 3.45/1.00  --bmc1_axioms                           reachable_all
% 3.45/1.00  --bmc1_min_bound                        0
% 3.45/1.00  --bmc1_max_bound                        -1
% 3.45/1.00  --bmc1_max_bound_default                -1
% 3.45/1.00  --bmc1_symbol_reachability              true
% 3.45/1.00  --bmc1_property_lemmas                  false
% 3.45/1.00  --bmc1_k_induction                      false
% 3.45/1.00  --bmc1_non_equiv_states                 false
% 3.45/1.00  --bmc1_deadlock                         false
% 3.45/1.00  --bmc1_ucm                              false
% 3.45/1.00  --bmc1_add_unsat_core                   none
% 3.45/1.00  --bmc1_unsat_core_children              false
% 3.45/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/1.00  --bmc1_out_stat                         full
% 3.45/1.00  --bmc1_ground_init                      false
% 3.45/1.00  --bmc1_pre_inst_next_state              false
% 3.45/1.00  --bmc1_pre_inst_state                   false
% 3.45/1.00  --bmc1_pre_inst_reach_state             false
% 3.45/1.00  --bmc1_out_unsat_core                   false
% 3.45/1.00  --bmc1_aig_witness_out                  false
% 3.45/1.00  --bmc1_verbose                          false
% 3.45/1.00  --bmc1_dump_clauses_tptp                false
% 3.45/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.45/1.00  --bmc1_dump_file                        -
% 3.45/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.45/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.45/1.00  --bmc1_ucm_extend_mode                  1
% 3.45/1.00  --bmc1_ucm_init_mode                    2
% 3.45/1.00  --bmc1_ucm_cone_mode                    none
% 3.45/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.45/1.00  --bmc1_ucm_relax_model                  4
% 3.45/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.45/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/1.00  --bmc1_ucm_layered_model                none
% 3.45/1.00  --bmc1_ucm_max_lemma_size               10
% 3.45/1.00  
% 3.45/1.00  ------ AIG Options
% 3.45/1.00  
% 3.45/1.00  --aig_mode                              false
% 3.45/1.00  
% 3.45/1.00  ------ Instantiation Options
% 3.45/1.00  
% 3.45/1.00  --instantiation_flag                    true
% 3.45/1.00  --inst_sos_flag                         false
% 3.45/1.00  --inst_sos_phase                        true
% 3.45/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/1.00  --inst_lit_sel_side                     none
% 3.45/1.00  --inst_solver_per_active                1400
% 3.45/1.00  --inst_solver_calls_frac                1.
% 3.45/1.00  --inst_passive_queue_type               priority_queues
% 3.45/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/1.00  --inst_passive_queues_freq              [25;2]
% 3.45/1.00  --inst_dismatching                      true
% 3.45/1.00  --inst_eager_unprocessed_to_passive     true
% 3.45/1.00  --inst_prop_sim_given                   true
% 3.45/1.00  --inst_prop_sim_new                     false
% 3.45/1.00  --inst_subs_new                         false
% 3.45/1.00  --inst_eq_res_simp                      false
% 3.45/1.00  --inst_subs_given                       false
% 3.45/1.00  --inst_orphan_elimination               true
% 3.45/1.00  --inst_learning_loop_flag               true
% 3.45/1.00  --inst_learning_start                   3000
% 3.45/1.00  --inst_learning_factor                  2
% 3.45/1.00  --inst_start_prop_sim_after_learn       3
% 3.45/1.00  --inst_sel_renew                        solver
% 3.45/1.00  --inst_lit_activity_flag                true
% 3.45/1.00  --inst_restr_to_given                   false
% 3.45/1.00  --inst_activity_threshold               500
% 3.45/1.00  --inst_out_proof                        true
% 3.45/1.00  
% 3.45/1.00  ------ Resolution Options
% 3.45/1.00  
% 3.45/1.00  --resolution_flag                       false
% 3.45/1.00  --res_lit_sel                           adaptive
% 3.45/1.00  --res_lit_sel_side                      none
% 3.45/1.00  --res_ordering                          kbo
% 3.45/1.00  --res_to_prop_solver                    active
% 3.45/1.00  --res_prop_simpl_new                    false
% 3.45/1.00  --res_prop_simpl_given                  true
% 3.45/1.00  --res_passive_queue_type                priority_queues
% 3.45/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/1.00  --res_passive_queues_freq               [15;5]
% 3.45/1.00  --res_forward_subs                      full
% 3.45/1.00  --res_backward_subs                     full
% 3.45/1.00  --res_forward_subs_resolution           true
% 3.45/1.00  --res_backward_subs_resolution          true
% 3.45/1.00  --res_orphan_elimination                true
% 3.45/1.00  --res_time_limit                        2.
% 3.45/1.00  --res_out_proof                         true
% 3.45/1.00  
% 3.45/1.00  ------ Superposition Options
% 3.45/1.00  
% 3.45/1.00  --superposition_flag                    true
% 3.45/1.00  --sup_passive_queue_type                priority_queues
% 3.45/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.45/1.00  --demod_completeness_check              fast
% 3.45/1.00  --demod_use_ground                      true
% 3.45/1.00  --sup_to_prop_solver                    passive
% 3.45/1.00  --sup_prop_simpl_new                    true
% 3.45/1.00  --sup_prop_simpl_given                  true
% 3.45/1.00  --sup_fun_splitting                     false
% 3.45/1.00  --sup_smt_interval                      50000
% 3.45/1.00  
% 3.45/1.00  ------ Superposition Simplification Setup
% 3.45/1.00  
% 3.45/1.00  --sup_indices_passive                   []
% 3.45/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_full_bw                           [BwDemod]
% 3.45/1.00  --sup_immed_triv                        [TrivRules]
% 3.45/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_immed_bw_main                     []
% 3.45/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.00  
% 3.45/1.00  ------ Combination Options
% 3.45/1.00  
% 3.45/1.00  --comb_res_mult                         3
% 3.45/1.00  --comb_sup_mult                         2
% 3.45/1.00  --comb_inst_mult                        10
% 3.45/1.00  
% 3.45/1.00  ------ Debug Options
% 3.45/1.00  
% 3.45/1.00  --dbg_backtrace                         false
% 3.45/1.00  --dbg_dump_prop_clauses                 false
% 3.45/1.00  --dbg_dump_prop_clauses_file            -
% 3.45/1.00  --dbg_out_stat                          false
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  ------ Proving...
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  % SZS status Theorem for theBenchmark.p
% 3.45/1.00  
% 3.45/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.45/1.00  
% 3.45/1.00  fof(f13,conjecture,(
% 3.45/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f14,negated_conjecture,(
% 3.45/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.45/1.00    inference(negated_conjecture,[],[f13])).
% 3.45/1.00  
% 3.45/1.00  fof(f32,plain,(
% 3.45/1.00    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.45/1.00    inference(ennf_transformation,[],[f14])).
% 3.45/1.00  
% 3.45/1.00  fof(f33,plain,(
% 3.45/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.45/1.00    inference(flattening,[],[f32])).
% 3.45/1.00  
% 3.45/1.00  fof(f39,plain,(
% 3.45/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.45/1.00    introduced(choice_axiom,[])).
% 3.45/1.00  
% 3.45/1.00  fof(f40,plain,(
% 3.45/1.00    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.45/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f39])).
% 3.45/1.00  
% 3.45/1.00  fof(f66,plain,(
% 3.45/1.00    r1_tarski(sK2,sK0)),
% 3.45/1.00    inference(cnf_transformation,[],[f40])).
% 3.45/1.00  
% 3.45/1.00  fof(f10,axiom,(
% 3.45/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f26,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/1.00    inference(ennf_transformation,[],[f10])).
% 3.45/1.00  
% 3.45/1.00  fof(f27,plain,(
% 3.45/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/1.00    inference(flattening,[],[f26])).
% 3.45/1.00  
% 3.45/1.00  fof(f38,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/1.00    inference(nnf_transformation,[],[f27])).
% 3.45/1.00  
% 3.45/1.00  fof(f54,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f38])).
% 3.45/1.00  
% 3.45/1.00  fof(f64,plain,(
% 3.45/1.00    v1_funct_2(sK3,sK0,sK1)),
% 3.45/1.00    inference(cnf_transformation,[],[f40])).
% 3.45/1.00  
% 3.45/1.00  fof(f65,plain,(
% 3.45/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.45/1.00    inference(cnf_transformation,[],[f40])).
% 3.45/1.00  
% 3.45/1.00  fof(f8,axiom,(
% 3.45/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f23,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/1.00    inference(ennf_transformation,[],[f8])).
% 3.45/1.00  
% 3.45/1.00  fof(f52,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f23])).
% 3.45/1.00  
% 3.45/1.00  fof(f5,axiom,(
% 3.45/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f19,plain,(
% 3.45/1.00    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.45/1.00    inference(ennf_transformation,[],[f5])).
% 3.45/1.00  
% 3.45/1.00  fof(f20,plain,(
% 3.45/1.00    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.45/1.00    inference(flattening,[],[f19])).
% 3.45/1.00  
% 3.45/1.00  fof(f49,plain,(
% 3.45/1.00    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f20])).
% 3.45/1.00  
% 3.45/1.00  fof(f6,axiom,(
% 3.45/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f21,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/1.00    inference(ennf_transformation,[],[f6])).
% 3.45/1.00  
% 3.45/1.00  fof(f50,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f21])).
% 3.45/1.00  
% 3.45/1.00  fof(f12,axiom,(
% 3.45/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f30,plain,(
% 3.45/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.45/1.00    inference(ennf_transformation,[],[f12])).
% 3.45/1.00  
% 3.45/1.00  fof(f31,plain,(
% 3.45/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.45/1.00    inference(flattening,[],[f30])).
% 3.45/1.00  
% 3.45/1.00  fof(f62,plain,(
% 3.45/1.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f31])).
% 3.45/1.00  
% 3.45/1.00  fof(f63,plain,(
% 3.45/1.00    v1_funct_1(sK3)),
% 3.45/1.00    inference(cnf_transformation,[],[f40])).
% 3.45/1.00  
% 3.45/1.00  fof(f11,axiom,(
% 3.45/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f28,plain,(
% 3.45/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.45/1.00    inference(ennf_transformation,[],[f11])).
% 3.45/1.00  
% 3.45/1.00  fof(f29,plain,(
% 3.45/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.45/1.00    inference(flattening,[],[f28])).
% 3.45/1.00  
% 3.45/1.00  fof(f61,plain,(
% 3.45/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f29])).
% 3.45/1.00  
% 3.45/1.00  fof(f9,axiom,(
% 3.45/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f24,plain,(
% 3.45/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.45/1.00    inference(ennf_transformation,[],[f9])).
% 3.45/1.00  
% 3.45/1.00  fof(f25,plain,(
% 3.45/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.45/1.00    inference(flattening,[],[f24])).
% 3.45/1.00  
% 3.45/1.00  fof(f53,plain,(
% 3.45/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f25])).
% 3.45/1.00  
% 3.45/1.00  fof(f1,axiom,(
% 3.45/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f34,plain,(
% 3.45/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.45/1.00    inference(nnf_transformation,[],[f1])).
% 3.45/1.00  
% 3.45/1.00  fof(f35,plain,(
% 3.45/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.45/1.00    inference(flattening,[],[f34])).
% 3.45/1.00  
% 3.45/1.00  fof(f41,plain,(
% 3.45/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.45/1.00    inference(cnf_transformation,[],[f35])).
% 3.45/1.00  
% 3.45/1.00  fof(f70,plain,(
% 3.45/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.45/1.00    inference(equality_resolution,[],[f41])).
% 3.45/1.00  
% 3.45/1.00  fof(f56,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f38])).
% 3.45/1.00  
% 3.45/1.00  fof(f68,plain,(
% 3.45/1.00    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.45/1.00    inference(cnf_transformation,[],[f40])).
% 3.45/1.00  
% 3.45/1.00  fof(f60,plain,(
% 3.45/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f29])).
% 3.45/1.00  
% 3.45/1.00  fof(f57,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f38])).
% 3.45/1.00  
% 3.45/1.00  fof(f76,plain,(
% 3.45/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.45/1.00    inference(equality_resolution,[],[f57])).
% 3.45/1.00  
% 3.45/1.00  fof(f3,axiom,(
% 3.45/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f36,plain,(
% 3.45/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.45/1.00    inference(nnf_transformation,[],[f3])).
% 3.45/1.00  
% 3.45/1.00  fof(f37,plain,(
% 3.45/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.45/1.00    inference(flattening,[],[f36])).
% 3.45/1.00  
% 3.45/1.00  fof(f46,plain,(
% 3.45/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.45/1.00    inference(cnf_transformation,[],[f37])).
% 3.45/1.00  
% 3.45/1.00  fof(f72,plain,(
% 3.45/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.45/1.00    inference(equality_resolution,[],[f46])).
% 3.45/1.00  
% 3.45/1.00  fof(f59,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f38])).
% 3.45/1.00  
% 3.45/1.00  fof(f73,plain,(
% 3.45/1.00    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.00    inference(equality_resolution,[],[f59])).
% 3.45/1.00  
% 3.45/1.00  fof(f74,plain,(
% 3.45/1.00    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.45/1.00    inference(equality_resolution,[],[f73])).
% 3.45/1.00  
% 3.45/1.00  fof(f47,plain,(
% 3.45/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.45/1.00    inference(cnf_transformation,[],[f37])).
% 3.45/1.00  
% 3.45/1.00  fof(f71,plain,(
% 3.45/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.45/1.00    inference(equality_resolution,[],[f47])).
% 3.45/1.00  
% 3.45/1.00  fof(f67,plain,(
% 3.45/1.00    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.45/1.00    inference(cnf_transformation,[],[f40])).
% 3.45/1.00  
% 3.45/1.00  fof(f45,plain,(
% 3.45/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f37])).
% 3.45/1.00  
% 3.45/1.00  fof(f2,axiom,(
% 3.45/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f16,plain,(
% 3.45/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.45/1.00    inference(ennf_transformation,[],[f2])).
% 3.45/1.00  
% 3.45/1.00  fof(f44,plain,(
% 3.45/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f16])).
% 3.45/1.00  
% 3.45/1.00  fof(f55,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f38])).
% 3.45/1.00  
% 3.45/1.00  fof(f77,plain,(
% 3.45/1.00    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.45/1.00    inference(equality_resolution,[],[f55])).
% 3.45/1.00  
% 3.45/1.00  cnf(c_24,negated_conjecture,
% 3.45/1.00      ( r1_tarski(sK2,sK0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_979,plain,
% 3.45/1.00      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_18,plain,
% 3.45/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.45/1.00      | k1_xboole_0 = X2 ),
% 3.45/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_26,negated_conjecture,
% 3.45/1.00      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_406,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.45/1.00      | sK3 != X0
% 3.45/1.00      | sK1 != X2
% 3.45/1.00      | sK0 != X1
% 3.45/1.00      | k1_xboole_0 = X2 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_407,plain,
% 3.45/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.45/1.00      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.45/1.00      | k1_xboole_0 = sK1 ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_406]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_25,negated_conjecture,
% 3.45/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.45/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_409,plain,
% 3.45/1.00      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_407,c_25]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_978,plain,
% 3.45/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_984,plain,
% 3.45/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.45/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2046,plain,
% 3.45/1.00      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_978,c_984]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2143,plain,
% 3.45/1.00      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_409,c_2046]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8,plain,
% 3.45/1.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.45/1.00      | ~ v1_relat_1(X1)
% 3.45/1.00      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_986,plain,
% 3.45/1.00      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.45/1.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.45/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2598,plain,
% 3.45/1.00      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.45/1.00      | sK1 = k1_xboole_0
% 3.45/1.00      | r1_tarski(X0,sK0) != iProver_top
% 3.45/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_2143,c_986]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_30,plain,
% 3.45/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_9,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | v1_relat_1(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1171,plain,
% 3.45/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.45/1.00      | v1_relat_1(sK3) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1172,plain,
% 3.45/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.45/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1171]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2758,plain,
% 3.45/1.00      ( r1_tarski(X0,sK0) != iProver_top
% 3.45/1.00      | sK1 = k1_xboole_0
% 3.45/1.00      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_2598,c_30,c_1172]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2759,plain,
% 3.45/1.00      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.45/1.00      | sK1 = k1_xboole_0
% 3.45/1.00      | r1_tarski(X0,sK0) != iProver_top ),
% 3.45/1.00      inference(renaming,[status(thm)],[c_2758]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2768,plain,
% 3.45/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_979,c_2759]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_21,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | ~ v1_funct_1(X0)
% 3.45/1.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.45/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_980,plain,
% 3.45/1.00      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.45/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.45/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3612,plain,
% 3.45/1.00      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.45/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_978,c_980]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_27,negated_conjecture,
% 3.45/1.00      ( v1_funct_1(sK3) ),
% 3.45/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1243,plain,
% 3.45/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.45/1.00      | ~ v1_funct_1(sK3)
% 3.45/1.00      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2011,plain,
% 3.45/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.45/1.00      | ~ v1_funct_1(sK3)
% 3.45/1.00      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_1243]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3729,plain,
% 3.45/1.00      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_3612,c_27,c_25,c_2011]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_19,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | ~ v1_funct_1(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_982,plain,
% 3.45/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.45/1.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.45/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3785,plain,
% 3.45/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.45/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.45/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_3729,c_982]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_28,plain,
% 3.45/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5141,plain,
% 3.45/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_3785,c_28,c_30]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_12,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.45/1.00      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 3.45/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_983,plain,
% 3.45/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.45/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 3.45/1.00      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5153,plain,
% 3.45/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 3.45/1.00      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_5141,c_983]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2,plain,
% 3.45/1.00      ( r1_tarski(X0,X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_988,plain,
% 3.45/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5957,plain,
% 3.45/1.00      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X1)) = k1_relat_1(k7_relat_1(sK3,X1))
% 3.45/1.00      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X0) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_5153,c_984]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_7234,plain,
% 3.45/1.00      ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_988,c_5957]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_7257,plain,
% 3.45/1.00      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 3.45/1.00      | sK1 = k1_xboole_0 ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_2768,c_7234]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_16,plain,
% 3.45/1.00      ( v1_funct_2(X0,X1,X2)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.45/1.00      | k1_xboole_0 = X2 ),
% 3.45/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_22,negated_conjecture,
% 3.45/1.00      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.45/1.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.45/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.45/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_390,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.45/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.45/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.45/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.45/1.00      | sK2 != X1
% 3.45/1.00      | sK1 != X2
% 3.45/1.00      | k1_xboole_0 = X2 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_391,plain,
% 3.45/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.45/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.45/1.00      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.45/1.00      | k1_xboole_0 = sK1 ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_390]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_971,plain,
% 3.45/1.00      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.45/1.00      | k1_xboole_0 = sK1
% 3.45/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.45/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3736,plain,
% 3.45/1.00      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 3.45/1.00      | sK1 = k1_xboole_0
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.45/1.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_3729,c_971]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_20,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | ~ v1_funct_1(X0)
% 3.45/1.00      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.45/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_981,plain,
% 3.45/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.45/1.00      | v1_funct_1(X0) != iProver_top
% 3.45/1.00      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1859,plain,
% 3.45/1.00      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.45/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_978,c_981]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1206,plain,
% 3.45/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.45/1.00      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 3.45/1.00      | ~ v1_funct_1(sK3) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1515,plain,
% 3.45/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.45/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 3.45/1.00      | ~ v1_funct_1(sK3) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_1206]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1516,plain,
% 3.45/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.45/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.45/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1515]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2146,plain,
% 3.45/1.00      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_1859,c_28,c_30,c_1516]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3737,plain,
% 3.45/1.00      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_3729,c_2146]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3744,plain,
% 3.45/1.00      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 3.45/1.00      | sK1 = k1_xboole_0
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.45/1.00      inference(forward_subsumption_resolution,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_3736,c_3737]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_7412,plain,
% 3.45/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.45/1.00      | sK1 = k1_xboole_0
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_7257,c_3744]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_7494,plain,
% 3.45/1.00      ( sK1 = k1_xboole_0
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_7412,c_2768]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_7501,plain,
% 3.45/1.00      ( sK1 = k1_xboole_0
% 3.45/1.00      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_5153,c_7494]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11342,plain,
% 3.45/1.00      ( sK1 = k1_xboole_0 | r1_tarski(sK2,sK2) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_2768,c_7501]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4074,plain,
% 3.45/1.00      ( r1_tarski(sK2,sK2) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4077,plain,
% 3.45/1.00      ( r1_tarski(sK2,sK2) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_4074]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11345,plain,
% 3.45/1.00      ( sK1 = k1_xboole_0 ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_11342,c_4077]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_15,plain,
% 3.45/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.45/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_358,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.45/1.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.45/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.45/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.45/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.45/1.00      | sK2 != k1_xboole_0
% 3.45/1.00      | sK1 != X1 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_359,plain,
% 3.45/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.45/1.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.45/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.45/1.00      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.45/1.00      | sK2 != k1_xboole_0 ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_358]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_973,plain,
% 3.45/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.45/1.00      | sK2 != k1_xboole_0
% 3.45/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.45/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.45/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_359]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5,plain,
% 3.45/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1113,plain,
% 3.45/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.45/1.00      | sK2 != k1_xboole_0
% 3.45/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.45/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.45/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_973,c_5]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3733,plain,
% 3.45/1.00      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.45/1.00      | sK2 != k1_xboole_0
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.45/1.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_3729,c_1113]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3773,plain,
% 3.45/1.00      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.45/1.00      | sK2 != k1_xboole_0
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.45/1.00      inference(forward_subsumption_resolution,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_3733,c_3737]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11383,plain,
% 3.45/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.45/1.00      | sK2 != k1_xboole_0
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_11345,c_3773]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_13,plain,
% 3.45/1.00      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.45/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.45/1.00      | k1_xboole_0 = X0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_312,plain,
% 3.45/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.45/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.45/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.45/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.45/1.00      | sK2 != X0
% 3.45/1.00      | sK1 != k1_xboole_0
% 3.45/1.00      | k1_xboole_0 = X0 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_313,plain,
% 3.45/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.45/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.45/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.45/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.45/1.00      | sK1 != k1_xboole_0
% 3.45/1.00      | k1_xboole_0 = sK2 ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_312]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_975,plain,
% 3.45/1.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.45/1.00      | sK1 != k1_xboole_0
% 3.45/1.00      | k1_xboole_0 = sK2
% 3.45/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.45/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.45/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4,plain,
% 3.45/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1100,plain,
% 3.45/1.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.45/1.00      | sK2 = k1_xboole_0
% 3.45/1.00      | sK1 != k1_xboole_0
% 3.45/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.45/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.45/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_975,c_4]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3734,plain,
% 3.45/1.00      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.45/1.00      | sK2 = k1_xboole_0
% 3.45/1.00      | sK1 != k1_xboole_0
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.45/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.45/1.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_3729,c_1100]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3762,plain,
% 3.45/1.00      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.45/1.00      | sK2 = k1_xboole_0
% 3.45/1.00      | sK1 != k1_xboole_0
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.45/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.45/1.00      inference(forward_subsumption_resolution,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_3734,c_3737]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_23,negated_conjecture,
% 3.45/1.00      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_6,plain,
% 3.45/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.45/1.00      | k1_xboole_0 = X0
% 3.45/1.00      | k1_xboole_0 = X1 ),
% 3.45/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_76,plain,
% 3.45/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.45/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_77,plain,
% 3.45/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_624,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1199,plain,
% 3.45/1.00      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_624]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1415,plain,
% 3.45/1.00      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_1199]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_623,plain,( X0 = X0 ),theory(equality) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1416,plain,
% 3.45/1.00      ( sK2 = sK2 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_623]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1846,plain,
% 3.45/1.00      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_624]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1847,plain,
% 3.45/1.00      ( sK1 != k1_xboole_0
% 3.45/1.00      | k1_xboole_0 = sK1
% 3.45/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_1846]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3,plain,
% 3.45/1.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1891,plain,
% 3.45/1.00      ( ~ r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_625,plain,
% 3.45/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.45/1.00      theory(equality) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1356,plain,
% 3.45/1.00      ( ~ r1_tarski(X0,X1)
% 3.45/1.00      | r1_tarski(sK2,k1_xboole_0)
% 3.45/1.00      | sK2 != X0
% 3.45/1.00      | k1_xboole_0 != X1 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_625]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2139,plain,
% 3.45/1.00      ( ~ r1_tarski(sK2,X0)
% 3.45/1.00      | r1_tarski(sK2,k1_xboole_0)
% 3.45/1.00      | sK2 != sK2
% 3.45/1.00      | k1_xboole_0 != X0 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_1356]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4079,plain,
% 3.45/1.00      ( ~ r1_tarski(sK2,sK0)
% 3.45/1.00      | r1_tarski(sK2,k1_xboole_0)
% 3.45/1.00      | sK2 != sK2
% 3.45/1.00      | k1_xboole_0 != sK0 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_2139]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_6807,plain,
% 3.45/1.00      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_3762,c_24,c_23,c_76,c_77,c_1415,c_1416,c_1847,c_1891,
% 3.45/1.00                 c_4079]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11384,plain,
% 3.45/1.00      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_11345,c_6807]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11486,plain,
% 3.45/1.00      ( sK2 = k1_xboole_0 ),
% 3.45/1.00      inference(equality_resolution_simp,[status(thm)],[c_11384]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11495,plain,
% 3.45/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 3.45/1.00      | k1_xboole_0 != k1_xboole_0
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.45/1.00      inference(light_normalisation,[status(thm)],[c_11383,c_11486]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11496,plain,
% 3.45/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.45/1.00      inference(equality_resolution_simp,[status(thm)],[c_11495]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5151,plain,
% 3.45/1.00      ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_5141,c_984]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11394,plain,
% 3.45/1.00      ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_11345,c_5151]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11413,plain,
% 3.45/1.00      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_11345,c_23]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11414,plain,
% 3.45/1.00      ( sK0 = k1_xboole_0 ),
% 3.45/1.00      inference(equality_resolution_simp,[status(thm)],[c_11413]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11464,plain,
% 3.45/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.45/1.00      inference(light_normalisation,[status(thm)],[c_11394,c_11414]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11497,plain,
% 3.45/1.00      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_11496,c_11464]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11399,plain,
% 3.45/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_11345,c_5141]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11459,plain,
% 3.45/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.45/1.00      inference(light_normalisation,[status(thm)],[c_11399,c_11414]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11461,plain,
% 3.45/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_11459,c_5]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11501,plain,
% 3.45/1.00      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.45/1.00      inference(forward_subsumption_resolution,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_11497,c_11461]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11502,plain,
% 3.45/1.00      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_11501,c_5]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11408,plain,
% 3.45/1.00      ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_11345,c_2046]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_17,plain,
% 3.45/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.45/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_377,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.45/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.45/1.00      | sK3 != X0
% 3.45/1.00      | sK1 != X1
% 3.45/1.00      | sK0 != k1_xboole_0 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_378,plain,
% 3.45/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.45/1.00      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.45/1.00      | sK0 != k1_xboole_0 ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_377]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_972,plain,
% 3.45/1.00      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.45/1.00      | sK0 != k1_xboole_0
% 3.45/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_378]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1044,plain,
% 3.45/1.00      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.45/1.00      | sK0 != k1_xboole_0
% 3.45/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_972,c_5]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11410,plain,
% 3.45/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 3.45/1.00      | sK0 != k1_xboole_0
% 3.45/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_11345,c_1044]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11421,plain,
% 3.45/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 3.45/1.00      | k1_xboole_0 != k1_xboole_0
% 3.45/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.45/1.00      inference(light_normalisation,[status(thm)],[c_11410,c_11414]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11422,plain,
% 3.45/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 3.45/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.45/1.00      inference(equality_resolution_simp,[status(thm)],[c_11421]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11412,plain,
% 3.45/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_11345,c_978]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11417,plain,
% 3.45/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.45/1.00      inference(light_normalisation,[status(thm)],[c_11412,c_11414]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11419,plain,
% 3.45/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_11417,c_5]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11425,plain,
% 3.45/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 3.45/1.00      inference(forward_subsumption_resolution,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_11422,c_11419]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11428,plain,
% 3.45/1.00      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.45/1.00      inference(light_normalisation,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_11408,c_11414,c_11425]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_629,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.45/1.00      theory(equality) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1331,plain,
% 3.45/1.00      ( m1_subset_1(X0,X1)
% 3.45/1.00      | ~ m1_subset_1(k2_partfun1(X2,X3,sK3,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.45/1.00      | X0 != k2_partfun1(X2,X3,sK3,X4)
% 3.45/1.00      | X1 != k1_zfmisc_1(k2_zfmisc_1(X2,X3)) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_629]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1550,plain,
% 3.45/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.45/1.00      | ~ m1_subset_1(k2_partfun1(X2,X3,sK3,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.45/1.00      | X0 != k2_partfun1(X2,X3,sK3,X4)
% 3.45/1.00      | k1_zfmisc_1(X1) != k1_zfmisc_1(k2_zfmisc_1(X2,X3)) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_1331]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_10432,plain,
% 3.45/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(X1))
% 3.45/1.00      | k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
% 3.45/1.00      | k1_zfmisc_1(X1) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_1550]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_10433,plain,
% 3.45/1.00      ( k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
% 3.45/1.00      | k1_zfmisc_1(X1) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 3.45/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_10432]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_10435,plain,
% 3.45/1.00      ( k7_relat_1(sK3,k1_xboole_0) != k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
% 3.45/1.00      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 3.45/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.45/1.00      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_10433]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2083,plain,
% 3.45/1.00      ( X0 != X1
% 3.45/1.00      | X0 = k2_zfmisc_1(sK0,sK1)
% 3.45/1.00      | k2_zfmisc_1(sK0,sK1) != X1 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_624]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_6783,plain,
% 3.45/1.00      ( X0 != k2_zfmisc_1(X1,X2)
% 3.45/1.00      | X0 = k2_zfmisc_1(sK0,sK1)
% 3.45/1.00      | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X1,X2) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_2083]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_6788,plain,
% 3.45/1.00      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 3.45/1.00      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
% 3.45/1.00      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_6783]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4895,plain,
% 3.45/1.00      ( k7_relat_1(sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_623]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4897,plain,
% 3.45/1.00      ( k7_relat_1(sK3,k1_xboole_0) = k7_relat_1(sK3,k1_xboole_0) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_4895]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1802,plain,
% 3.45/1.00      ( X0 != X1
% 3.45/1.00      | X0 = k2_partfun1(sK0,sK1,sK3,X2)
% 3.45/1.00      | k2_partfun1(sK0,sK1,sK3,X2) != X1 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_624]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3443,plain,
% 3.45/1.00      ( X0 = k2_partfun1(sK0,sK1,sK3,X1)
% 3.45/1.00      | X0 != k7_relat_1(sK3,X1)
% 3.45/1.00      | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_1802]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4894,plain,
% 3.45/1.00      ( k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
% 3.45/1.00      | k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
% 3.45/1.00      | k7_relat_1(sK3,X0) != k7_relat_1(sK3,X0) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_3443]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4896,plain,
% 3.45/1.00      ( k2_partfun1(sK0,sK1,sK3,k1_xboole_0) != k7_relat_1(sK3,k1_xboole_0)
% 3.45/1.00      | k7_relat_1(sK3,k1_xboole_0) = k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
% 3.45/1.00      | k7_relat_1(sK3,k1_xboole_0) != k7_relat_1(sK3,k1_xboole_0) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_4894]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_626,plain,
% 3.45/1.00      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 3.45/1.00      theory(equality) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4168,plain,
% 3.45/1.00      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(X0,X1)
% 3.45/1.00      | sK1 != X1
% 3.45/1.00      | sK0 != X0 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_626]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4170,plain,
% 3.45/1.00      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 3.45/1.00      | sK1 != k1_xboole_0
% 3.45/1.00      | sK0 != k1_xboole_0 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_4168]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2299,plain,
% 3.45/1.00      ( X0 != X1 | X0 = k2_zfmisc_1(X2,X3) | k2_zfmisc_1(X2,X3) != X1 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_624]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2300,plain,
% 3.45/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.45/1.00      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 3.45/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_2299]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2013,plain,
% 3.45/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.45/1.00      | ~ v1_funct_1(sK3)
% 3.45/1.00      | k2_partfun1(sK0,sK1,sK3,k1_xboole_0) = k7_relat_1(sK3,k1_xboole_0) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_2011]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1238,plain,
% 3.45/1.00      ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.45/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.45/1.00      | ~ v1_funct_1(sK3) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1520,plain,
% 3.45/1.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.45/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.45/1.00      | ~ v1_funct_1(sK3) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_1238]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1521,plain,
% 3.45/1.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.45/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.45/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1520]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1523,plain,
% 3.45/1.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.45/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.45/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_1521]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1482,plain,
% 3.45/1.00      ( ~ r1_tarski(X0,X1)
% 3.45/1.00      | r1_tarski(X2,k1_relat_1(sK3))
% 3.45/1.00      | X2 != X0
% 3.45/1.00      | k1_relat_1(sK3) != X1 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_625]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1484,plain,
% 3.45/1.00      ( r1_tarski(k1_xboole_0,k1_relat_1(sK3))
% 3.45/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.45/1.00      | k1_relat_1(sK3) != k1_xboole_0
% 3.45/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_1482]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_628,plain,
% 3.45/1.00      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.45/1.00      theory(equality) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1462,plain,
% 3.45/1.00      ( X0 != k2_zfmisc_1(sK0,sK1)
% 3.45/1.00      | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_628]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1467,plain,
% 3.45/1.00      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 3.45/1.00      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_1462]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1437,plain,
% 3.45/1.00      ( sK0 = sK0 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_623]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1200,plain,
% 3.45/1.00      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_624]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1436,plain,
% 3.45/1.00      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_1200]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1248,plain,
% 3.45/1.00      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 3.45/1.00      | ~ v1_relat_1(sK3)
% 3.45/1.00      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1250,plain,
% 3.45/1.00      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
% 3.45/1.00      | ~ v1_relat_1(sK3)
% 3.45/1.00      | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_1248]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_82,plain,
% 3.45/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(contradiction,plain,
% 3.45/1.00      ( $false ),
% 3.45/1.00      inference(minisat,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_11502,c_11428,c_11342,c_10435,c_6788,c_4897,c_4896,
% 3.45/1.00                 c_4170,c_4077,c_2300,c_2013,c_1847,c_1523,c_1484,c_1467,
% 3.45/1.00                 c_1437,c_1436,c_1250,c_1171,c_82,c_77,c_76,c_23,c_30,
% 3.45/1.00                 c_25,c_28,c_27]) ).
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.45/1.00  
% 3.45/1.00  ------                               Statistics
% 3.45/1.00  
% 3.45/1.00  ------ General
% 3.45/1.00  
% 3.45/1.00  abstr_ref_over_cycles:                  0
% 3.45/1.00  abstr_ref_under_cycles:                 0
% 3.45/1.00  gc_basic_clause_elim:                   0
% 3.45/1.00  forced_gc_time:                         0
% 3.45/1.00  parsing_time:                           0.009
% 3.45/1.00  unif_index_cands_time:                  0.
% 3.45/1.00  unif_index_add_time:                    0.
% 3.45/1.00  orderings_time:                         0.
% 3.45/1.00  out_proof_time:                         0.015
% 3.45/1.00  total_time:                             0.35
% 3.45/1.00  num_of_symbols:                         48
% 3.45/1.00  num_of_terms:                           11528
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing
% 3.45/1.00  
% 3.45/1.00  num_of_splits:                          0
% 3.45/1.00  num_of_split_atoms:                     0
% 3.45/1.00  num_of_reused_defs:                     0
% 3.45/1.00  num_eq_ax_congr_red:                    13
% 3.45/1.00  num_of_sem_filtered_clauses:            1
% 3.45/1.00  num_of_subtypes:                        0
% 3.45/1.00  monotx_restored_types:                  0
% 3.45/1.00  sat_num_of_epr_types:                   0
% 3.45/1.00  sat_num_of_non_cyclic_types:            0
% 3.45/1.00  sat_guarded_non_collapsed_types:        0
% 3.45/1.00  num_pure_diseq_elim:                    0
% 3.45/1.00  simp_replaced_by:                       0
% 3.45/1.00  res_preprocessed:                       123
% 3.45/1.00  prep_upred:                             0
% 3.45/1.00  prep_unflattend:                        35
% 3.45/1.00  smt_new_axioms:                         0
% 3.45/1.00  pred_elim_cands:                        4
% 3.45/1.00  pred_elim:                              2
% 3.45/1.00  pred_elim_cl:                           2
% 3.45/1.00  pred_elim_cycles:                       5
% 3.45/1.00  merged_defs:                            0
% 3.45/1.00  merged_defs_ncl:                        0
% 3.45/1.00  bin_hyper_res:                          0
% 3.45/1.00  prep_cycles:                            4
% 3.45/1.00  pred_elim_time:                         0.006
% 3.45/1.00  splitting_time:                         0.
% 3.45/1.00  sem_filter_time:                        0.
% 3.45/1.00  monotx_time:                            0.
% 3.45/1.00  subtype_inf_time:                       0.
% 3.45/1.00  
% 3.45/1.00  ------ Problem properties
% 3.45/1.00  
% 3.45/1.00  clauses:                                25
% 3.45/1.00  conjectures:                            4
% 3.45/1.00  epr:                                    6
% 3.45/1.00  horn:                                   22
% 3.45/1.00  ground:                                 11
% 3.45/1.00  unary:                                  6
% 3.45/1.00  binary:                                 6
% 3.45/1.00  lits:                                   65
% 3.45/1.00  lits_eq:                                29
% 3.45/1.00  fd_pure:                                0
% 3.45/1.00  fd_pseudo:                              0
% 3.45/1.00  fd_cond:                                2
% 3.45/1.00  fd_pseudo_cond:                         1
% 3.45/1.00  ac_symbols:                             0
% 3.45/1.00  
% 3.45/1.00  ------ Propositional Solver
% 3.45/1.00  
% 3.45/1.00  prop_solver_calls:                      30
% 3.45/1.00  prop_fast_solver_calls:                 1159
% 3.45/1.00  smt_solver_calls:                       0
% 3.45/1.00  smt_fast_solver_calls:                  0
% 3.45/1.00  prop_num_of_clauses:                    4540
% 3.45/1.00  prop_preprocess_simplified:             10206
% 3.45/1.00  prop_fo_subsumed:                       35
% 3.45/1.00  prop_solver_time:                       0.
% 3.45/1.00  smt_solver_time:                        0.
% 3.45/1.00  smt_fast_solver_time:                   0.
% 3.45/1.00  prop_fast_solver_time:                  0.
% 3.45/1.00  prop_unsat_core_time:                   0.
% 3.45/1.00  
% 3.45/1.00  ------ QBF
% 3.45/1.00  
% 3.45/1.00  qbf_q_res:                              0
% 3.45/1.00  qbf_num_tautologies:                    0
% 3.45/1.00  qbf_prep_cycles:                        0
% 3.45/1.00  
% 3.45/1.00  ------ BMC1
% 3.45/1.00  
% 3.45/1.00  bmc1_current_bound:                     -1
% 3.45/1.00  bmc1_last_solved_bound:                 -1
% 3.45/1.00  bmc1_unsat_core_size:                   -1
% 3.45/1.00  bmc1_unsat_core_parents_size:           -1
% 3.45/1.00  bmc1_merge_next_fun:                    0
% 3.45/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.45/1.00  
% 3.45/1.00  ------ Instantiation
% 3.45/1.00  
% 3.45/1.00  inst_num_of_clauses:                    1608
% 3.45/1.01  inst_num_in_passive:                    534
% 3.45/1.01  inst_num_in_active:                     655
% 3.45/1.01  inst_num_in_unprocessed:                419
% 3.45/1.01  inst_num_of_loops:                      720
% 3.45/1.01  inst_num_of_learning_restarts:          0
% 3.45/1.01  inst_num_moves_active_passive:          62
% 3.45/1.01  inst_lit_activity:                      0
% 3.45/1.01  inst_lit_activity_moves:                0
% 3.45/1.01  inst_num_tautologies:                   0
% 3.45/1.01  inst_num_prop_implied:                  0
% 3.45/1.01  inst_num_existing_simplified:           0
% 3.45/1.01  inst_num_eq_res_simplified:             0
% 3.45/1.01  inst_num_child_elim:                    0
% 3.45/1.01  inst_num_of_dismatching_blockings:      512
% 3.45/1.01  inst_num_of_non_proper_insts:           1645
% 3.45/1.01  inst_num_of_duplicates:                 0
% 3.45/1.01  inst_inst_num_from_inst_to_res:         0
% 3.45/1.01  inst_dismatching_checking_time:         0.
% 3.45/1.01  
% 3.45/1.01  ------ Resolution
% 3.45/1.01  
% 3.45/1.01  res_num_of_clauses:                     0
% 3.45/1.01  res_num_in_passive:                     0
% 3.45/1.01  res_num_in_active:                      0
% 3.45/1.01  res_num_of_loops:                       127
% 3.45/1.01  res_forward_subset_subsumed:            80
% 3.45/1.01  res_backward_subset_subsumed:           4
% 3.45/1.01  res_forward_subsumed:                   0
% 3.45/1.01  res_backward_subsumed:                  0
% 3.45/1.01  res_forward_subsumption_resolution:     0
% 3.45/1.01  res_backward_subsumption_resolution:    0
% 3.45/1.01  res_clause_to_clause_subsumption:       697
% 3.45/1.01  res_orphan_elimination:                 0
% 3.45/1.01  res_tautology_del:                      91
% 3.45/1.01  res_num_eq_res_simplified:              1
% 3.45/1.01  res_num_sel_changes:                    0
% 3.45/1.01  res_moves_from_active_to_pass:          0
% 3.45/1.01  
% 3.45/1.01  ------ Superposition
% 3.45/1.01  
% 3.45/1.01  sup_time_total:                         0.
% 3.45/1.01  sup_time_generating:                    0.
% 3.45/1.01  sup_time_sim_full:                      0.
% 3.45/1.01  sup_time_sim_immed:                     0.
% 3.45/1.01  
% 3.45/1.01  sup_num_of_clauses:                     139
% 3.45/1.01  sup_num_in_active:                      57
% 3.45/1.01  sup_num_in_passive:                     82
% 3.45/1.01  sup_num_of_loops:                       143
% 3.45/1.01  sup_fw_superposition:                   187
% 3.45/1.01  sup_bw_superposition:                   100
% 3.45/1.01  sup_immediate_simplified:               117
% 3.45/1.01  sup_given_eliminated:                   0
% 3.45/1.01  comparisons_done:                       0
% 3.45/1.01  comparisons_avoided:                    129
% 3.45/1.01  
% 3.45/1.01  ------ Simplifications
% 3.45/1.01  
% 3.45/1.01  
% 3.45/1.01  sim_fw_subset_subsumed:                 22
% 3.45/1.01  sim_bw_subset_subsumed:                 8
% 3.45/1.01  sim_fw_subsumed:                        20
% 3.45/1.01  sim_bw_subsumed:                        0
% 3.45/1.01  sim_fw_subsumption_res:                 13
% 3.45/1.01  sim_bw_subsumption_res:                 0
% 3.45/1.01  sim_tautology_del:                      2
% 3.45/1.01  sim_eq_tautology_del:                   62
% 3.45/1.01  sim_eq_res_simp:                        6
% 3.45/1.01  sim_fw_demodulated:                     15
% 3.45/1.01  sim_bw_demodulated:                     80
% 3.45/1.01  sim_light_normalised:                   70
% 3.45/1.01  sim_joinable_taut:                      0
% 3.45/1.01  sim_joinable_simp:                      0
% 3.45/1.01  sim_ac_normalised:                      0
% 3.45/1.01  sim_smt_subsumption:                    0
% 3.45/1.01  
%------------------------------------------------------------------------------
